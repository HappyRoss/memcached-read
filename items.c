/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
#include "memcached.h"
#include "bipbuffer.h"
#include "slab_automove.h"
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/resource.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <errno.h>
#include <stdlib.h>
#include <stdio.h>
#include <signal.h>
#include <string.h>
#include <time.h>
#include <assert.h>
#include <unistd.h>
#include <poll.h>

/* Forward Declarations */
static void item_link_q(item *it);
static void item_unlink_q(item *it);

static unsigned int lru_type_map[4] = {HOT_LRU, WARM_LRU, COLD_LRU, TEMP_LRU};

#define LARGEST_ID POWER_LARGEST
typedef struct {
    uint64_t evicted;
    uint64_t evicted_nonzero;
    uint64_t reclaimed;
    uint64_t outofmemory;
    uint64_t tailrepairs;
    uint64_t expired_unfetched; /* items reclaimed but never touched */
    uint64_t evicted_unfetched; /* items evicted but never touched */
    uint64_t evicted_active; /* items evicted that should have been shuffled */
    uint64_t crawler_reclaimed;
    uint64_t crawler_items_checked;
    uint64_t lrutail_reflocked;
    uint64_t moves_to_cold;
    uint64_t moves_to_warm;
    uint64_t moves_within_lru;
    uint64_t direct_reclaims;
    uint64_t hits_to_hot;
    uint64_t hits_to_warm;
    uint64_t hits_to_cold;
    uint64_t hits_to_temp;
    rel_time_t evicted_time;
} itemstats_t;

static item *heads[LARGEST_ID];//指向每一个LRU队列头
static item *tails[LARGEST_ID];//指向每一个LRU队列尾
static itemstats_t itemstats[LARGEST_ID];
static unsigned int sizes[LARGEST_ID];//每一个LRU队列有多少个item
static uint64_t sizes_bytes[LARGEST_ID];//每一个LRU队列占用了多少btyes
static unsigned int *stats_sizes_hist = NULL;
static uint64_t stats_sizes_cas_min = 0;
static int stats_sizes_buckets = 0;

static volatile int do_run_lru_maintainer_thread = 0;
static int lru_maintainer_initialized = 0;
static pthread_mutex_t lru_maintainer_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t cas_id_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t stats_sizes_lock = PTHREAD_MUTEX_INITIALIZER;

void item_stats_reset(void) {
    int i;
    for (i = 0; i < LARGEST_ID; i++) {
        pthread_mutex_lock(&lru_locks[i]);
        memset(&itemstats[i], 0, sizeof(itemstats_t));
        pthread_mutex_unlock(&lru_locks[i]);
    }
}

/* called with class lru lock held */
void do_item_stats_add_crawl(const int i, const uint64_t reclaimed,
        const uint64_t unfetched, const uint64_t checked) {
    itemstats[i].crawler_reclaimed += reclaimed;
    itemstats[i].expired_unfetched += unfetched;
    itemstats[i].crawler_items_checked += checked;
}

typedef struct _lru_bump_buf {
    struct _lru_bump_buf *prev;
    struct _lru_bump_buf *next;
    pthread_mutex_t mutex;
    bipbuf_t *buf;
    uint64_t dropped;
} lru_bump_buf;

typedef struct {
    item *it;
    uint32_t hv;
} lru_bump_entry;

static lru_bump_buf *bump_buf_head = NULL;
static lru_bump_buf *bump_buf_tail = NULL;
static pthread_mutex_t bump_buf_lock = PTHREAD_MUTEX_INITIALIZER;
/* TODO: tunable? Need bench results */
#define LRU_BUMP_BUF_SIZE 8192

static bool lru_bump_async(lru_bump_buf *b, item *it, uint32_t hv);
static uint64_t lru_total_bumps_dropped(void);

/* Get the next CAS id for a new item. */
/* TODO: refactor some atomics for this. */
uint64_t get_cas_id(void) {
    static uint64_t cas_id = 0;
    pthread_mutex_lock(&cas_id_lock);
    uint64_t next_id = ++cas_id;
    pthread_mutex_unlock(&cas_id_lock);
    return next_id;
}

int item_is_flushed(item *it) {
    rel_time_t oldest_live = settings.oldest_live;//需要删除item的时刻 全局变量settings的oldest_live成员存储接收到worker线程接收到flush_all命令时刻-1
    uint64_t cas = ITEM_get_cas(it);
    uint64_t oldest_cas = settings.oldest_cas;
    if (oldest_live == 0 || oldest_live > current_time)//不用删除item
        return 0;
    if ((it->time <= oldest_live)
            || (oldest_cas != 0 && cas != 0 && cas < oldest_cas)) {//需删除item 刷新
        return 1;
    }
    return 0;
}

static unsigned int temp_lru_size(int slabs_clsid) {
    int id = CLEAR_LRU(slabs_clsid);
    id |= TEMP_LRU;
    unsigned int ret;
    pthread_mutex_lock(&lru_locks[id]);
    ret = sizes_bytes[id];
    pthread_mutex_unlock(&lru_locks[id]);
    return ret;
}

/* Enable this for reference-count debugging. */
#if 0
# define DEBUG_REFCNT(it,op) \
                fprintf(stderr, "item %x refcnt(%c) %d %c%c%c\n", \
                        it, op, it->refcount, \
                        (it->it_flags & ITEM_LINKED) ? 'L' : ' ', \
                        (it->it_flags & ITEM_SLABBED) ? 'S' : ' ')
#else
# define DEBUG_REFCNT(it,op) while(0)
#endif

/**
 * Generates the variable-sized part of the header for an object.
 *
 * key     - The key
 * nkey    - The length of the key
 * flags   - key flags
 * nbytes  - Number of bytes to hold value and addition CRLF terminator
 * suffix  - Buffer for the "VALUE" line suffix (flags, size).
 * nsuffix - The length of the suffix is stored here.
 *
 * Returns the total size of the header.
 */
static size_t item_make_header(const uint8_t nkey, const unsigned int flags, const int nbytes,
                     char *suffix, uint8_t *nsuffix) {
    if (settings.inline_ascii_response) {
        /* suffix is defined at 40 chars elsewhere.. */
        *nsuffix = (uint8_t) snprintf(suffix, 40, " %u %d\r\n", flags, nbytes - 2);
    } else {
        if (flags == 0) {
            *nsuffix = 0;
        } else {
            *nsuffix = sizeof(flags);
        }
    }
    return sizeof(item) + nkey + *nsuffix + nbytes;
}

item *do_item_alloc_pull(const size_t ntotal, const unsigned int id) {
    item *it = NULL;
    int i;
    /* If no memory is available, attempt a direct LRU juggle/eviction */
    /* This is a race in order to simplify lru_pull_tail; in cases where
     * locked items are on the tail, you want them to fall out and cause
     * occasional OOM's, rather than internally work around them.
     * This also gives one fewer code path for slab alloc/free
     */
    for (i = 0; i < 10; i++) {
        uint64_t total_bytes;
        /* Try to reclaim memory first */ //先尝试回收内存
        if (!settings.lru_segmented) {
            lru_pull_tail(id, COLD_LRU, 0, 0, 0, NULL);
        }
        it = slabs_alloc(ntotal, id, &total_bytes, 0);

        if (settings.temp_lru)
            total_bytes -= temp_lru_size(id);

        if (it == NULL) {
            if (lru_pull_tail(id, COLD_LRU, total_bytes, LRU_PULL_EVICT, 0, NULL) <= 0) {
                if (settings.lru_segmented) {
                    lru_pull_tail(id, HOT_LRU, total_bytes, 0, 0, NULL);
                } else {
                    break;
                }
            }
        } else {
            break;
        }
    }

    if (i > 0) {
        pthread_mutex_lock(&lru_locks[id]);
        itemstats[id].direct_reclaims += i;
        pthread_mutex_unlock(&lru_locks[id]);
    }

    return it;
}

/* Chain another chunk onto this chunk. */
/* slab mover: if it finds a chunk without ITEM_CHUNK flag, and no ITEM_LINKED
 * flag, it counts as busy and skips.
 * I think it might still not be safe to do linking outside of the slab lock
 */
item_chunk *do_item_alloc_chunk(item_chunk *ch, const size_t bytes_remain) {
    // TODO: Should be a cleaner way of finding real size with slabber calls
    size_t size = bytes_remain + sizeof(item_chunk);
    if (size > settings.slab_chunk_size_max)
        size = settings.slab_chunk_size_max;
    unsigned int id = slabs_clsid(size);

    item_chunk *nch = (item_chunk *) do_item_alloc_pull(size, id);
    if (nch == NULL)
        return NULL;

    // link in.
    // ITEM_CHUNK[ED] bits need to be protected by the slabs lock.
    slabs_mlock();
    nch->head = ch->head;
    ch->next = nch;
    nch->prev = ch;
    nch->next = 0;
    nch->used = 0;
    nch->slabs_clsid = id;
    nch->size = size - sizeof(item_chunk);
    nch->it_flags |= ITEM_CHUNK;
    slabs_munlock();
    return nch;
}

item *do_item_alloc(char *key, const size_t nkey, const unsigned int flags,
                    const rel_time_t exptime, const int nbytes) {
    uint8_t nsuffix;
    item *it = NULL;
    char suffix[40];
    // Avoid potential underflows.
    if (nbytes < 2)
        return 0;

    size_t ntotal = item_make_header(nkey + 1, flags, nbytes, suffix, &nsuffix);//存储item大小的空间
    if (settings.use_cas) {
        ntotal += sizeof(uint64_t);
    }

    unsigned int id = slabs_clsid(ntotal);//找大小为ntotal的item在slabclass数组的下标 即根据item大小判断其属于哪个slab  如果返回0 表示出错了
    unsigned int hdr_id = 0;
    if (id == 0)
        return 0;

    /* This is a large item. Allocate a header object now, lazily allocate
     *  chunks while reading the upload.
     */
    if (ntotal > settings.slab_chunk_size_max) {//注意这里比较的是settings.slab_chunk_size_max 而在slabs_clsid中比较的settings.item_size_max
        /* We still link this item into the LRU for the larger slab class, but
         * we're pulling a header from an entirely different slab class. The
         * free routines handle large items specifically.
         */
        int htotal = nkey + 1 + nsuffix + sizeof(item) + sizeof(item_chunk);
        if (settings.use_cas) {
            htotal += sizeof(uint64_t);
        }
        hdr_id = slabs_clsid(htotal);
        it = do_item_alloc_pull(htotal, hdr_id);
        /* setting ITEM_CHUNKED is fine here because we aren't LINKED yet. */
        if (it != NULL)
            it->it_flags |= ITEM_CHUNKED;
    } else {
        it = do_item_alloc_pull(ntotal, id);//item大小 item属于第id个slab
    }

    if (it == NULL) {
        pthread_mutex_lock(&lru_locks[id]);
        itemstats[id].outofmemory++;
        pthread_mutex_unlock(&lru_locks[id]);
        return NULL;
    }

    assert(it->slabs_clsid == 0);
    //assert(it != heads[id]);

    /* Refcount is seeded to 1 by slabs_alloc() */
    it->next = it->prev = 0;

    /* Items are initially loaded into the HOT_LRU. This is '0' but I want at
     * least a note here. Compiler (hopefully?) optimizes this out.
     */
    if (settings.temp_lru &&
            exptime - current_time <= settings.temporary_ttl) {
        id |= TEMP_LRU;
    } else if (settings.lru_segmented) {
        id |= HOT_LRU;
    } else {
        /* There is only COLD in compat-mode */
        id |= COLD_LRU;
    }
    it->slabs_clsid = id;

    DEBUG_REFCNT(it, '*');
    it->it_flags |= settings.use_cas ? ITEM_CAS : 0;
    it->nkey = nkey;
    it->nbytes = nbytes;
    memcpy(ITEM_key(it), key, nkey);
    it->exptime = exptime;
    if (settings.inline_ascii_response) {
        memcpy(ITEM_suffix(it), suffix, (size_t)nsuffix);
    } else if (nsuffix > 0) {
        memcpy(ITEM_suffix(it), &flags, sizeof(flags));
    }
    it->nsuffix = nsuffix;

    /* Initialize internal chunk. */
    if (it->it_flags & ITEM_CHUNKED) {
        item_chunk *chunk = (item_chunk *) ITEM_data(it);

        chunk->next = 0;
        chunk->prev = 0;
        chunk->used = 0;
        chunk->size = 0;
        chunk->head = it;
        chunk->orig_clsid = hdr_id;
    }
    it->h_next = 0;

    return it;
}

void item_free(item *it) {
    size_t ntotal = ITEM_ntotal(it);
    unsigned int clsid;
    assert((it->it_flags & ITEM_LINKED) == 0);
    assert(it != heads[it->slabs_clsid]);
    assert(it != tails[it->slabs_clsid]);
    assert(it->refcount == 0);

    /* so slab size changer can tell later if item is already free or not */
    clsid = ITEM_clsid(it);//ITEM_clsid用于计算出it在slabclass数组的位置
    DEBUG_REFCNT(it, 'F');
    slabs_free(it, ntotal, clsid);
}

/**
 * Returns true if an item will fit in the cache (its size does not exceed
 * the maximum for a cache entry.)
 */
bool item_size_ok(const size_t nkey, const int flags, const int nbytes) {
    char prefix[40];
    uint8_t nsuffix;
    if (nbytes < 2)
        return false;

    size_t ntotal = item_make_header(nkey + 1, flags, nbytes,
                                     prefix, &nsuffix);
    if (settings.use_cas) {
        ntotal += sizeof(uint64_t);
    }

    return slabs_clsid(ntotal) != 0;
}

static void do_item_link_q(item *it) { /* item is the new head */ //memcached插入操作耗时是常数
    item **head, **tail;
    assert((it->it_flags & ITEM_SLABBED) == 0);

    head = &heads[it->slabs_clsid];//LRU队列的头
    tail = &tails[it->slabs_clsid];//LRU队列的尾
    assert(it != *head);
    assert((*head && *tail) || (*head == 0 && *tail == 0));
    it->prev = 0;//it的prev为0
    it->next = *head;//it的next指向队列头
    if (it->next) it->next->prev = it;//如果it的next不为NULL 则设置it的next指向item的prev指向it
    *head = it;//更新队列头指向
    if (*tail == 0) *tail = it;//判断队列尾是否为NULL 如果是则队列尾指向it
    sizes[it->slabs_clsid]++;//item大小为it->slabs_clsid的队列的item个数加1
    sizes_bytes[it->slabs_clsid] += ITEM_ntotal(it);//item大小为it->slabs_clsid的队列的bytes数
    return;
}

static void item_link_q(item *it) {//将item插入到LRU队列的头部
    pthread_mutex_lock(&lru_locks[it->slabs_clsid]);//获取item类型为it->slabs_clsid的LRU队列的锁
    do_item_link_q(it);//插入具体操作
    pthread_mutex_unlock(&lru_locks[it->slabs_clsid]);//释放锁
}

static void item_link_q_warm(item *it) {
    pthread_mutex_lock(&lru_locks[it->slabs_clsid]);
    do_item_link_q(it);
    itemstats[it->slabs_clsid].moves_to_warm++;//统计数据 移往warm队列的数量加1
    pthread_mutex_unlock(&lru_locks[it->slabs_clsid]);
}

static void do_item_unlink_q(item *it) {//将it从对应的LRU队列中删除 //memcached插入操作耗时是常数
    item **head, **tail;
    head = &heads[it->slabs_clsid];//item大小为it->slabs_clsid的队列头
    tail = &tails[it->slabs_clsid];//item大小为it->slabs_clsid的队列尾

    if (*head == it) {//如果it是队列头
        assert(it->prev == 0);
        *head = it->next;
    }
    if (*tail == it) {//如果it是队列尾
        assert(it->next == 0);
        *tail = it->prev;
    }
    assert(it->next != it);
    assert(it->prev != it);

    if (it->next) it->next->prev = it->prev;//如果it的next不为NULL
    if (it->prev) it->prev->next = it->next;//如果it的prev不为NULL
    sizes[it->slabs_clsid]--;//item大小为it->slabs_clsid的队列的item个数减1
    sizes_bytes[it->slabs_clsid] -= ITEM_ntotal(it);//item大小为it->slabs_clsid的队列bytes数减
    return;
}

static void item_unlink_q(item *it) {//将it从对应的LRU队列中删除
    pthread_mutex_lock(&lru_locks[it->slabs_clsid]);//获取item大小为it->slabs_clsid队列的锁
    do_item_unlink_q(it);//删除具体操作
    pthread_mutex_unlock(&lru_locks[it->slabs_clsid]);//释放锁
}

int do_item_link(item *it, const uint32_t hv) {
    MEMCACHED_ITEM_LINK(ITEM_key(it), it->nkey, it->nbytes);
    assert((it->it_flags & (ITEM_LINKED|ITEM_SLABBED)) == 0);
    it->it_flags |= ITEM_LINKED;
    it->time = current_time;

    STATS_LOCK();
    stats_state.curr_bytes += ITEM_ntotal(it);
    stats_state.curr_items += 1;
    stats.total_items += 1;
    STATS_UNLOCK();

    /* Allocate a new CAS ID on link. */
    ITEM_set_cas(it, (settings.use_cas) ? get_cas_id() : 0);
    assoc_insert(it, hv);
    item_link_q(it);
    refcount_incr(it);
    item_stats_sizes_add(it);

    return 1;
}

void do_item_unlink(item *it, const uint32_t hv) {
    MEMCACHED_ITEM_UNLINK(ITEM_key(it), it->nkey, it->nbytes);
    if ((it->it_flags & ITEM_LINKED) != 0) {
        it->it_flags &= ~ITEM_LINKED;
        STATS_LOCK();
        stats_state.curr_bytes -= ITEM_ntotal(it);//修改统计
        stats_state.curr_items -= 1;
        STATS_UNLOCK();
        item_stats_sizes_remove(it);//stats_sizes_hist统计修改
        assoc_delete(ITEM_key(it), it->nkey, hv);//将it从hash表中移除
        item_unlink_q(it);//将it从对应的LRU队列中删除
        do_item_remove(it);
    }
}

/* FIXME: Is it necessary to keep this copy/pasted code? */
void do_item_unlink_nolock(item *it, const uint32_t hv) {
    MEMCACHED_ITEM_UNLINK(ITEM_key(it), it->nkey, it->nbytes);
    if ((it->it_flags & ITEM_LINKED) != 0) {//it的it_flags设置了ITEM_LINKED
        it->it_flags &= ~ITEM_LINKED;//it的it_flags取消ITEM_LINKED的设置
        STATS_LOCK();
        stats_state.curr_bytes -= ITEM_ntotal(it);
        stats_state.curr_items -= 1;
        STATS_UNLOCK();
        item_stats_sizes_remove(it);
        assoc_delete(ITEM_key(it), it->nkey, hv);//将it从其所在hash表中移除
        do_item_unlink_q(it);//将it从其所在的LRU队列中移除
        do_item_remove(it);//it应用计数减1 如果计算为0 则回收it 将it移到所在slabclass的数组中空闲list p->slots中
    }
}

void do_item_remove(item *it) {
    MEMCACHED_ITEM_REMOVE(ITEM_key(it), it->nkey, it->nbytes);
    assert((it->it_flags & ITEM_SLABBED) == 0);
    assert(it->refcount > 0);

    if (refcount_decr(it) == 0) {//如果应用计数为0 则删除item 即回收  --(it->refcount
        item_free(it);//it回收 回收到it所在slabclass的数组中空闲list p->slots中
    }
}

/* Copy/paste to avoid adding two extra branches for all common calls, since
 * _nolock is only used in an uncommon case where we want to relink. */
void do_item_update_nolock(item *it) {
    MEMCACHED_ITEM_UPDATE(ITEM_key(it), it->nkey, it->nbytes);
    if (it->time < current_time - ITEM_UPDATE_INTERVAL) {
        assert((it->it_flags & ITEM_SLABBED) == 0);

        if ((it->it_flags & ITEM_LINKED) != 0) {
            do_item_unlink_q(it);
            it->time = current_time;
            do_item_link_q(it);
        }
    }
}

/* Bump the last accessed time, or relink if we're in compat mode */
void do_item_update(item *it) {
    MEMCACHED_ITEM_UPDATE(ITEM_key(it), it->nkey, it->nbytes);

    /* Hits to COLD_LRU immediately move to WARM. */
    if (settings.lru_segmented) {
        assert((it->it_flags & ITEM_SLABBED) == 0);
        if ((it->it_flags & ITEM_LINKED) != 0) {//是判断it是否已链接？
            if (ITEM_lruid(it) == COLD_LRU && (it->it_flags & ITEM_ACTIVE)) {//item在cold队列 且 item状态是active 需将其移往warm队列
                it->time = current_time;//最近访问时间
                item_unlink_q(it);//删除it 将it从对应的LRU队列中删除 从cold队列中删除
                it->slabs_clsid = ITEM_clsid(it);//设置it的slabs_clsid
                it->slabs_clsid |= WARM_LRU;//使得it成为warm队列一个item 当在计算it所在队列时
                it->it_flags &= ~ITEM_ACTIVE;//设置it的it_flags 删除ITEM_ACTIVE
                item_link_q_warm(it);//it插入 warm队列LRU
            } else if (it->time < current_time - ITEM_UPDATE_INTERVAL) {//距离上次访问的时间超过了ITEM_UPDATE_INTERVAL 60
                it->time = current_time;
            }
        }
    } else if (it->time < current_time - ITEM_UPDATE_INTERVAL) {//距离上次访问的时间超过了ITEM_UPDATE_INTERVAL 60 //update操作时耗时的 如果这个item频繁被访问 那么会导致过多的update 过多的一系列费时操作 此时更新时间间隔就出现 如果上一次的访问时间（也可以说是update时间）距离现在（current_time）还在更新间隔内 就不更新 超过才更新
        assert((it->it_flags & ITEM_SLABBED) == 0);

        if ((it->it_flags & ITEM_LINKED) != 0) {//it在linked状态？
            it->time = current_time;//更新访问时间
            item_unlink_q(it);//删除it 将it从对应的LRU队列中删除
            item_link_q(it);//插入it 将item插入到LRU队列的头部 即最近访问的item最有可能会再次被访问 所以将其放置所在队列LRU头部
        }
    }
}

int do_item_replace(item *it, item *new_it, const uint32_t hv) {
    MEMCACHED_ITEM_REPLACE(ITEM_key(it), it->nkey, it->nbytes,
                           ITEM_key(new_it), new_it->nkey, new_it->nbytes);
    assert((it->it_flags & ITEM_SLABBED) == 0);

    do_item_unlink(it, hv);
    return do_item_link(new_it, hv);
}

/*@null@*/
/* This is walking the line of violating lock order, but I think it's safe.
 * If the LRU lock is held, an item in the LRU cannot be wiped and freed.
 * The data could possibly be overwritten, but this is only accessing the
 * headers.
 * It may not be the best idea to leave it like this, but for now it's safe.
 */
char *item_cachedump(const unsigned int slabs_clsid, const unsigned int limit, unsigned int *bytes) {
    unsigned int memlimit = 2 * 1024 * 1024;   /* 2MB max response size */
    char *buffer;
    unsigned int bufcurr;
    item *it;
    unsigned int len;
    unsigned int shown = 0;
    char key_temp[KEY_MAX_LENGTH + 1];
    char temp[512];
    unsigned int id = slabs_clsid;
    id |= COLD_LRU;

    pthread_mutex_lock(&lru_locks[id]);
    it = heads[id];

    buffer = malloc((size_t)memlimit);
    if (buffer == 0) {
        return NULL;
    }
    bufcurr = 0;

    while (it != NULL && (limit == 0 || shown < limit)) {
        assert(it->nkey <= KEY_MAX_LENGTH);
        if (it->nbytes == 0 && it->nkey == 0) {
            it = it->next;
            continue;
        }
        /* Copy the key since it may not be null-terminated in the struct */
        strncpy(key_temp, ITEM_key(it), it->nkey);
        key_temp[it->nkey] = 0x00; /* terminate */
        len = snprintf(temp, sizeof(temp), "ITEM %s [%d b; %llu s]\r\n",
                       key_temp, it->nbytes - 2,
                       it->exptime == 0 ? 0 :
                       (unsigned long long)it->exptime + process_started);
        if (bufcurr + len + 6 > memlimit)  /* 6 is END\r\n\0 */
            break;
        memcpy(buffer + bufcurr, temp, len);
        bufcurr += len;
        shown++;
        it = it->next;
    }

    memcpy(buffer + bufcurr, "END\r\n", 6);
    bufcurr += 5;

    *bytes = bufcurr;
    pthread_mutex_unlock(&lru_locks[id]);
    return buffer;
}

/* With refactoring of the various stats code the automover won't need a
 * custom function here.
 */
void fill_item_stats_automove(item_stats_automove *am) {
    int n;
    for (n = 0; n < MAX_NUMBER_OF_SLAB_CLASSES; n++) {
        item_stats_automove *cur = &am[n];

        // outofmemory records into HOT
        int i = n | HOT_LRU;
        pthread_mutex_lock(&lru_locks[i]);
        cur->outofmemory = itemstats[i].outofmemory;
        pthread_mutex_unlock(&lru_locks[i]);

        // evictions and tail age are from COLD
        i = n | COLD_LRU;
        pthread_mutex_lock(&lru_locks[i]);
        cur->evicted = itemstats[i].evicted;
        if (tails[i]) {
            cur->age = current_time - tails[i]->time;
        } else {
            cur->age = 0;
        }
        pthread_mutex_unlock(&lru_locks[i]);
     }
}

void item_stats_totals(ADD_STAT add_stats, void *c) {
    itemstats_t totals;
    memset(&totals, 0, sizeof(itemstats_t));
    int n;
    for (n = 0; n < MAX_NUMBER_OF_SLAB_CLASSES; n++) {
        int x;
        int i;
        for (x = 0; x < 4; x++) {
            i = n | lru_type_map[x];
            pthread_mutex_lock(&lru_locks[i]);
            totals.expired_unfetched += itemstats[i].expired_unfetched;
            totals.evicted_unfetched += itemstats[i].evicted_unfetched;
            totals.evicted_active += itemstats[i].evicted_active;
            totals.evicted += itemstats[i].evicted;
            totals.reclaimed += itemstats[i].reclaimed;
            totals.crawler_reclaimed += itemstats[i].crawler_reclaimed;
            totals.crawler_items_checked += itemstats[i].crawler_items_checked;
            totals.lrutail_reflocked += itemstats[i].lrutail_reflocked;
            totals.moves_to_cold += itemstats[i].moves_to_cold;
            totals.moves_to_warm += itemstats[i].moves_to_warm;
            totals.moves_within_lru += itemstats[i].moves_within_lru;
            totals.direct_reclaims += itemstats[i].direct_reclaims;
            pthread_mutex_unlock(&lru_locks[i]);
        }
    }
    APPEND_STAT("expired_unfetched", "%llu",
                (unsigned long long)totals.expired_unfetched);
    APPEND_STAT("evicted_unfetched", "%llu",
                (unsigned long long)totals.evicted_unfetched);
    if (settings.lru_maintainer_thread) {
        APPEND_STAT("evicted_active", "%llu",
                    (unsigned long long)totals.evicted_active);
    }
    APPEND_STAT("evictions", "%llu",
                (unsigned long long)totals.evicted);
    APPEND_STAT("reclaimed", "%llu",
                (unsigned long long)totals.reclaimed);
    APPEND_STAT("crawler_reclaimed", "%llu",
                (unsigned long long)totals.crawler_reclaimed);
    APPEND_STAT("crawler_items_checked", "%llu",
                (unsigned long long)totals.crawler_items_checked);
    APPEND_STAT("lrutail_reflocked", "%llu",
                (unsigned long long)totals.lrutail_reflocked);
    if (settings.lru_maintainer_thread) {
        APPEND_STAT("moves_to_cold", "%llu",
                    (unsigned long long)totals.moves_to_cold);
        APPEND_STAT("moves_to_warm", "%llu",
                    (unsigned long long)totals.moves_to_warm);
        APPEND_STAT("moves_within_lru", "%llu",
                    (unsigned long long)totals.moves_within_lru);
        APPEND_STAT("direct_reclaims", "%llu",
                    (unsigned long long)totals.direct_reclaims);
        APPEND_STAT("lru_bumps_dropped", "%llu",
                    (unsigned long long)lru_total_bumps_dropped());
    }
}

void item_stats(ADD_STAT add_stats, void *c) {
    struct thread_stats thread_stats;
    threadlocal_stats_aggregate(&thread_stats);
    itemstats_t totals;
    int n;
    for (n = 0; n < MAX_NUMBER_OF_SLAB_CLASSES; n++) {
        memset(&totals, 0, sizeof(itemstats_t));
        int x;
        int i;
        unsigned int size = 0;
        unsigned int age  = 0;
        unsigned int age_hot = 0;
        unsigned int age_warm = 0;
        unsigned int lru_size_map[4];
        const char *fmt = "items:%d:%s";
        char key_str[STAT_KEY_LEN];
        char val_str[STAT_VAL_LEN];
        int klen = 0, vlen = 0;
        for (x = 0; x < 4; x++) {
            i = n | lru_type_map[x];
            pthread_mutex_lock(&lru_locks[i]);
            totals.evicted += itemstats[i].evicted;
            totals.evicted_nonzero += itemstats[i].evicted_nonzero;
            totals.outofmemory += itemstats[i].outofmemory;
            totals.tailrepairs += itemstats[i].tailrepairs;
            totals.reclaimed += itemstats[i].reclaimed;
            totals.expired_unfetched += itemstats[i].expired_unfetched;
            totals.evicted_unfetched += itemstats[i].evicted_unfetched;
            totals.evicted_active += itemstats[i].evicted_active;
            totals.crawler_reclaimed += itemstats[i].crawler_reclaimed;
            totals.crawler_items_checked += itemstats[i].crawler_items_checked;
            totals.lrutail_reflocked += itemstats[i].lrutail_reflocked;
            totals.moves_to_cold += itemstats[i].moves_to_cold;
            totals.moves_to_warm += itemstats[i].moves_to_warm;
            totals.moves_within_lru += itemstats[i].moves_within_lru;
            totals.direct_reclaims += itemstats[i].direct_reclaims;
            size += sizes[i];
            lru_size_map[x] = sizes[i];
            if (lru_type_map[x] == COLD_LRU && tails[i] != NULL) {
                age = current_time - tails[i]->time;
            } else if (lru_type_map[x] == HOT_LRU && tails[i] != NULL) {
                age_hot = current_time - tails[i]->time;
            } else if (lru_type_map[x] == WARM_LRU && tails[i] != NULL) {
                age_warm = current_time - tails[i]->time;
            }
            if (lru_type_map[x] == COLD_LRU)
                totals.evicted_time = itemstats[i].evicted_time;
            switch (lru_type_map[x]) {
                case HOT_LRU:
                    totals.hits_to_hot = thread_stats.lru_hits[i];
                    break;
                case WARM_LRU:
                    totals.hits_to_warm = thread_stats.lru_hits[i];
                    break;
                case COLD_LRU:
                    totals.hits_to_cold = thread_stats.lru_hits[i];
                    break;
                case TEMP_LRU:
                    totals.hits_to_temp = thread_stats.lru_hits[i];
                    break;
            }
            pthread_mutex_unlock(&lru_locks[i]);
        }
        if (size == 0)
            continue;
        APPEND_NUM_FMT_STAT(fmt, n, "number", "%u", size);
        if (settings.lru_maintainer_thread) {
            APPEND_NUM_FMT_STAT(fmt, n, "number_hot", "%u", lru_size_map[0]);
            APPEND_NUM_FMT_STAT(fmt, n, "number_warm", "%u", lru_size_map[1]);
            APPEND_NUM_FMT_STAT(fmt, n, "number_cold", "%u", lru_size_map[2]);
            if (settings.temp_lru) {
                APPEND_NUM_FMT_STAT(fmt, n, "number_temp", "%u", lru_size_map[3]);
            }
            APPEND_NUM_FMT_STAT(fmt, n, "age_hot", "%u", age_hot);
            APPEND_NUM_FMT_STAT(fmt, n, "age_warm", "%u", age_warm);
        }
        APPEND_NUM_FMT_STAT(fmt, n, "age", "%u", age);
        APPEND_NUM_FMT_STAT(fmt, n, "evicted",
                            "%llu", (unsigned long long)totals.evicted);
        APPEND_NUM_FMT_STAT(fmt, n, "evicted_nonzero",
                            "%llu", (unsigned long long)totals.evicted_nonzero);
        APPEND_NUM_FMT_STAT(fmt, n, "evicted_time",
                            "%u", totals.evicted_time);
        APPEND_NUM_FMT_STAT(fmt, n, "outofmemory",
                            "%llu", (unsigned long long)totals.outofmemory);
        APPEND_NUM_FMT_STAT(fmt, n, "tailrepairs",
                            "%llu", (unsigned long long)totals.tailrepairs);
        APPEND_NUM_FMT_STAT(fmt, n, "reclaimed",
                            "%llu", (unsigned long long)totals.reclaimed);
        APPEND_NUM_FMT_STAT(fmt, n, "expired_unfetched",
                            "%llu", (unsigned long long)totals.expired_unfetched);
        APPEND_NUM_FMT_STAT(fmt, n, "evicted_unfetched",
                            "%llu", (unsigned long long)totals.evicted_unfetched);
        if (settings.lru_maintainer_thread) {
            APPEND_NUM_FMT_STAT(fmt, n, "evicted_active",
                                "%llu", (unsigned long long)totals.evicted_active);
        }
        APPEND_NUM_FMT_STAT(fmt, n, "crawler_reclaimed",
                            "%llu", (unsigned long long)totals.crawler_reclaimed);
        APPEND_NUM_FMT_STAT(fmt, n, "crawler_items_checked",
                            "%llu", (unsigned long long)totals.crawler_items_checked);
        APPEND_NUM_FMT_STAT(fmt, n, "lrutail_reflocked",
                            "%llu", (unsigned long long)totals.lrutail_reflocked);
        if (settings.lru_maintainer_thread) {
            APPEND_NUM_FMT_STAT(fmt, n, "moves_to_cold",
                                "%llu", (unsigned long long)totals.moves_to_cold);
            APPEND_NUM_FMT_STAT(fmt, n, "moves_to_warm",
                                "%llu", (unsigned long long)totals.moves_to_warm);
            APPEND_NUM_FMT_STAT(fmt, n, "moves_within_lru",
                                "%llu", (unsigned long long)totals.moves_within_lru);
            APPEND_NUM_FMT_STAT(fmt, n, "direct_reclaims",
                                "%llu", (unsigned long long)totals.direct_reclaims);
            APPEND_NUM_FMT_STAT(fmt, n, "hits_to_hot",
                                "%llu", (unsigned long long)totals.hits_to_hot);

            APPEND_NUM_FMT_STAT(fmt, n, "hits_to_warm",
                                "%llu", (unsigned long long)totals.hits_to_warm);

            APPEND_NUM_FMT_STAT(fmt, n, "hits_to_cold",
                                "%llu", (unsigned long long)totals.hits_to_cold);

            APPEND_NUM_FMT_STAT(fmt, n, "hits_to_temp",
                                "%llu", (unsigned long long)totals.hits_to_temp);

        }
    }

    /* getting here means both ascii and binary terminators fit */
    add_stats(NULL, 0, NULL, 0, c);
}

bool item_stats_sizes_status(void) {
    bool ret = false;
    mutex_lock(&stats_sizes_lock);
    if (stats_sizes_hist != NULL)
        ret = true;
    mutex_unlock(&stats_sizes_lock);
    return ret;
}

void item_stats_sizes_init(void) {
    if (stats_sizes_hist != NULL)
        return;
    stats_sizes_buckets = settings.item_size_max / 32 + 1;
    stats_sizes_hist = calloc(stats_sizes_buckets, sizeof(int));
    stats_sizes_cas_min = (settings.use_cas) ? get_cas_id() : 0;
}

void item_stats_sizes_enable(ADD_STAT add_stats, void *c) {
    mutex_lock(&stats_sizes_lock);
    if (!settings.use_cas) {
        APPEND_STAT("sizes_status", "error", "");
        APPEND_STAT("sizes_error", "cas_support_disabled", "");
    } else if (stats_sizes_hist == NULL) {
        item_stats_sizes_init();
        if (stats_sizes_hist != NULL) {
            APPEND_STAT("sizes_status", "enabled", "");
        } else {
            APPEND_STAT("sizes_status", "error", "");
            APPEND_STAT("sizes_error", "no_memory", "");
        }
    } else {
        APPEND_STAT("sizes_status", "enabled", "");
    }
    mutex_unlock(&stats_sizes_lock);
}

void item_stats_sizes_disable(ADD_STAT add_stats, void *c) {
    mutex_lock(&stats_sizes_lock);
    if (stats_sizes_hist != NULL) {
        free(stats_sizes_hist);
        stats_sizes_hist = NULL;
    }
    APPEND_STAT("sizes_status", "disabled", "");
    mutex_unlock(&stats_sizes_lock);
}

void item_stats_sizes_add(item *it) {
    if (stats_sizes_hist == NULL || stats_sizes_cas_min > ITEM_get_cas(it))
        return;
    int ntotal = ITEM_ntotal(it);
    int bucket = ntotal / 32;
    if ((ntotal % 32) != 0) bucket++;
    if (bucket < stats_sizes_buckets) stats_sizes_hist[bucket]++;
}

/* I think there's no way for this to be accurate without using the CAS value.
 * Since items getting their time value bumped will pass this validation.
 */
void item_stats_sizes_remove(item *it) {
    if (stats_sizes_hist == NULL || stats_sizes_cas_min > ITEM_get_cas(it))
        return;
    int ntotal = ITEM_ntotal(it);
    int bucket = ntotal / 32;//计算item（大小）在stats_sizes_hist中的下标
    if ((ntotal % 32) != 0) bucket++;//如果不能整除 则加1
    if (bucket < stats_sizes_buckets) stats_sizes_hist[bucket]--;//bucket在stats_sizes_hist范围内 下标bucket数量减1
}

/** dumps out a list of objects of each size, with granularity of 32 bytes */
/*@null@*/
/* Locks are correct based on a technicality. Holds LRU lock while doing the
 * work, so items can't go invalid, and it's only looking at header sizes
 * which don't change.
 */
void item_stats_sizes(ADD_STAT add_stats, void *c) {
    mutex_lock(&stats_sizes_lock);

    if (stats_sizes_hist != NULL) {
        int i;
        for (i = 0; i < stats_sizes_buckets; i++) {
            if (stats_sizes_hist[i] != 0) {
                char key[8];
                snprintf(key, sizeof(key), "%d", i * 32);
                APPEND_STAT(key, "%u", stats_sizes_hist[i]);
            }
        }
    } else {
        APPEND_STAT("sizes_status", "disabled", "");
    }

    add_stats(NULL, 0, NULL, 0, c);
    mutex_unlock(&stats_sizes_lock);
}

/** wrapper around assoc_find which does the lazy expiration logic */
item *do_item_get(const char *key, const size_t nkey, const uint32_t hv, conn *c, const bool do_update) {
    item *it = assoc_find(key, nkey, hv);
    if (it != NULL) {
        refcount_incr(it); //++(it->refcount)
        /* Optimization for slab reassignment. prevents popular items from
         * jamming in busy wait. Can only do this here to satisfy lock order
         * of item_lock, slabs_lock. */
        /* This was made unsafe by removal of the cache_lock:
         * slab_rebalance_signal and slab_rebal.* are modified in a separate
         * thread under slabs_lock. If slab_rebalance_signal = 1, slab_start =
         * NULL (0), but slab_end is still equal to some value, this would end
         * up unlinking every item fetched.
         * This is either an acceptable loss, or if slab_rebalance_signal is
         * true, slab_start/slab_end should be put behind the slabs_lock.
         * Which would cause a huge potential slowdown.
         * Could also use a specific lock for slab_rebal.* and
         * slab_rebalance_signal (shorter lock?)
         */
        /*if (slab_rebalance_signal &&
            ((void *)it >= slab_rebal.slab_start && (void *)it < slab_rebal.slab_end)) {
            do_item_unlink(it, hv);
            do_item_remove(it);
            it = NULL;
        }*/
    }
    int was_found = 0;

    if (settings.verbose > 2) {
        int ii;
        if (it == NULL) {
            fprintf(stderr, "> NOT FOUND ");
        } else {
            fprintf(stderr, "> FOUND KEY ");
        }
        for (ii = 0; ii < nkey; ++ii) {
            fprintf(stderr, "%c", key[ii]);
        }
    }

    if (it != NULL) {
        was_found = 1;//found
        if (item_is_flushed(it)) {//玩家通过命令设置所有item过期? 判断是否需删除item 刷新  
            do_item_unlink(it, hv);
            do_item_remove(it);
            it = NULL;
            pthread_mutex_lock(&c->thread->stats.mutex);//lock
            c->thread->stats.get_flushed++;
            pthread_mutex_unlock(&c->thread->stats.mutex);
            if (settings.verbose > 2) {
                fprintf(stderr, " -nuked by flush");
            }
            was_found = 2;
        } else if (it->exptime != 0 && it->exptime <= current_time) {//it过期了
            do_item_unlink(it, hv);
            do_item_remove(it);
            it = NULL;
            pthread_mutex_lock(&c->thread->stats.mutex);
            c->thread->stats.get_expired++;
            pthread_mutex_unlock(&c->thread->stats.mutex);
            if (settings.verbose > 2) {
                fprintf(stderr, " -nuked by expire");
            }
            was_found = 3;
        } else {
            if (do_update) {//更新
                /* We update the hit markers only during fetches.
                 * An item needs to be hit twice overall to be considered
                 * ACTIVE, but only needs a single hit to maintain activity
                 * afterward.
                 * FETCHED tells if an item has ever been active.
                 */
                if (settings.lru_segmented) {
                    if ((it->it_flags & ITEM_ACTIVE) == 0) {
                        if ((it->it_flags & ITEM_FETCHED) == 0) {
                            it->it_flags |= ITEM_FETCHED;//注 设置了it的it_flags
                        } else {
                            it->it_flags |= ITEM_ACTIVE;//注 设置了it的it_flags
                            if (ITEM_lruid(it) != COLD_LRU) {
                                do_item_update(it); // bump LA time
                            } else if (!lru_bump_async(c->thread->lru_bump_buf, it, hv)) {
                                // add flag before async bump to avoid race.
                                it->it_flags &= ~ITEM_ACTIVE;
                            }
                        }
                    }
                } else {
                    it->it_flags |= ITEM_FETCHED;
                    do_item_update(it);
                }
            }
            DEBUG_REFCNT(it, '+');
        }
    }

    if (settings.verbose > 2)
        fprintf(stderr, "\n");
    /* For now this is in addition to the above verbose logging. */
    LOGGER_LOG(c->thread->l, LOG_FETCHERS, LOGGER_ITEM_GET, NULL, was_found, key, nkey,
               (it) ? ITEM_clsid(it) : 0);

    return it;
}

item *do_item_touch(const char *key, size_t nkey, uint32_t exptime,
                    const uint32_t hv, conn *c) {
    item *it = do_item_get(key, nkey, hv, c, DO_UPDATE);
    if (it != NULL) {
        it->exptime = exptime;//有效时间
    }
    return it;
}

/*** LRU MAINTENANCE THREAD ***/

/* Returns number of items remove, expired, or evicted.
 * Callable from worker threads or the LRU maintainer thread */
int lru_pull_tail(const int orig_id, const int cur_lru,
        const uint64_t total_bytes, const uint8_t flags, const rel_time_t max_age,
        struct lru_pull_tail_return *ret_it) {
    item *it = NULL;
    int id = orig_id;//id
    int removed = 0;
    if (id == 0)
        return 0;

    int tries = 5;//
    item *search;
    item *next_it;
    void *hold_lock = NULL;
    unsigned int move_to_lru = 0;
    uint64_t limit = 0;

    id |= cur_lru;//id或上了cur_lru
    pthread_mutex_lock(&lru_locks[id]);//lock
    search = tails[id];//static item *tails[LARGEST_ID];//指向每一个LRU队列尾
    /* We walk up *only* for locked items, and if bottom is expired. */
    for (; tries > 0 && search != NULL; tries--, search=next_it) {
        /* we might relink search mid-loop, so search->prev isn't reliable */
        next_it = search->prev;
        if (search->nbytes == 0 && search->nkey == 0 && search->it_flags == 1) {
            /* We are a crawler, ignore it. */
            if (flags & LRU_PULL_CRAWL_BLOCKS) {//爬虫
                pthread_mutex_unlock(&lru_locks[id]);
                return 0;
            }
            tries++;
            continue;
        }
        uint32_t hv = hash(ITEM_key(search), search->nkey);//serch key的hash值
        /* Attempt to hash item lock the "search" item. If locked, no
         * other callers can incr the refcount. Also skip ourselves. */
        if ((hold_lock = item_trylock(hv)) == NULL)
            continue;
        /* Now see if the item is refcount locked */ //现在已经获取到了lock
        if (refcount_incr(search) != 2) {//判断search计数加1后是否等于2
            /* Note pathological case with ref'ed items in tail.
             * Can still unlink the item, but it won't be reusable yet */
            itemstats[id].lrutail_reflocked++;
            /* In case of refcount leaks, enable for quick workaround. */
            /* WARNING: This can cause terrible corruption */
            if (settings.tail_repair_time &&
                    search->time + settings.tail_repair_time < current_time) {
                itemstats[id].tailrepairs++;
                search->refcount = 1;//search的应用计数设置为1
                /* This will call item_remove -> item_free since refcnt is 1 */
                do_item_unlink_nolock(search, hv);
                item_trylock_unlock(hold_lock);
                continue;
            }
        }

        /* Expired or flushed */
        if ((search->exptime != 0 && search->exptime < current_time)
            || item_is_flushed(search)) {//expired or flushed
            itemstats[id].reclaimed++;
            if ((search->it_flags & ITEM_FETCHED) == 0) {
                itemstats[id].expired_unfetched++;
            }
            /* refcnt 2 -> 1 */
            do_item_unlink_nolock(search, hv);
            /* refcnt 1 -> 0 -> item_free */
            do_item_remove(search);
            item_trylock_unlock(hold_lock);
            removed++;

            /* If all we're finding are expired, can keep going */
            continue;
        }

        /* If we're HOT_LRU or WARM_LRU and over size limit, send to COLD_LRU.
         * If we're COLD_LRU, send to WARM_LRU unless we need to evict
         */
        switch (cur_lru) {
            case HOT_LRU:
                limit = total_bytes * settings.hot_lru_pct / 100;
            case WARM_LRU:
                if (limit == 0)
                    limit = total_bytes * settings.warm_lru_pct / 100;
                /* Rescue ACTIVE items aggressively */
                if ((search->it_flags & ITEM_ACTIVE) != 0) {
                    search->it_flags &= ~ITEM_ACTIVE;
                    removed++;
                    if (cur_lru == WARM_LRU) {
                        itemstats[id].moves_within_lru++;
                        do_item_update_nolock(search);
                        do_item_remove(search);
                        item_trylock_unlock(hold_lock);
                    } else {
                        /* Active HOT_LRU items flow to WARM */
                        itemstats[id].moves_to_warm++;
                        move_to_lru = WARM_LRU;
                        do_item_unlink_q(search);
                        it = search;
                    }
                } else if (sizes_bytes[id] > limit ||
                           current_time - search->time > max_age) {
                    itemstats[id].moves_to_cold++;
                    move_to_lru = COLD_LRU;
                    do_item_unlink_q(search);
                    it = search;
                    removed++;
                    break;
                } else {
                    /* Don't want to move to COLD, not active, bail out */
                    it = search;
                }
                break;
            case COLD_LRU:
                it = search; /* No matter what, we're stopping */
                if (flags & LRU_PULL_EVICT) {
                    if (settings.evict_to_free == 0) {
                        /* Don't think we need a counter for this. It'll OOM.  */
                        break;
                    }
                    itemstats[id].evicted++;
                    itemstats[id].evicted_time = current_time - search->time;
                    if (search->exptime != 0)
                        itemstats[id].evicted_nonzero++;
                    if ((search->it_flags & ITEM_FETCHED) == 0) {
                        itemstats[id].evicted_unfetched++;
                    }
                    if ((search->it_flags & ITEM_ACTIVE)) {
                        itemstats[id].evicted_active++;
                    }
                    LOGGER_LOG(NULL, LOG_EVICTIONS, LOGGER_EVICTION, search);
                    do_item_unlink_nolock(search, hv);
                    removed++;
                    if (settings.slab_automove == 2) {
                        slabs_reassign(-1, orig_id);
                    }
                } else if (flags & LRU_PULL_RETURN_ITEM) {
                    /* Keep a reference to this item and return it. */
                    ret_it->it = it;
                    ret_it->hv = hv;
                } else if ((search->it_flags & ITEM_ACTIVE) != 0
                        && settings.lru_segmented) {
                    itemstats[id].moves_to_warm++;
                    search->it_flags &= ~ITEM_ACTIVE;
                    move_to_lru = WARM_LRU;
                    do_item_unlink_q(search);
                    removed++;
                }
                break;
            case TEMP_LRU:
                it = search; /* Kill the loop. Parent only interested in reclaims */
                break;
        }
        if (it != NULL)
            break;
    }

    pthread_mutex_unlock(&lru_locks[id]);

    if (it != NULL) {
        if (move_to_lru) {
            it->slabs_clsid = ITEM_clsid(it);
            it->slabs_clsid |= move_to_lru;
            item_link_q(it);
        }
        if ((flags & LRU_PULL_RETURN_ITEM) == 0) {
            do_item_remove(it);
            item_trylock_unlock(hold_lock);
        }
    }

    return removed;
}


/* TODO: Third place this code needs to be deduped */
static void lru_bump_buf_link_q(lru_bump_buf *b) {
    pthread_mutex_lock(&bump_buf_lock);
    assert(b != bump_buf_head);

    b->prev = 0;
    b->next = bump_buf_head;
    if (b->next) b->next->prev = b;
    bump_buf_head = b;
    if (bump_buf_tail == 0) bump_buf_tail = b;
    pthread_mutex_unlock(&bump_buf_lock);
    return;
}

void *item_lru_bump_buf_create(void) {
    lru_bump_buf *b = calloc(1, sizeof(lru_bump_buf));
    if (b == NULL) {
        return NULL;
    }

    b->buf = bipbuf_new(sizeof(lru_bump_entry) * LRU_BUMP_BUF_SIZE);
    if (b->buf == NULL) {
        free(b);
        return NULL;
    }

    pthread_mutex_init(&b->mutex, NULL);

    lru_bump_buf_link_q(b);
    return b;
}

static bool lru_bump_async(lru_bump_buf *b, item *it, uint32_t hv) {
    bool ret = true;
    refcount_incr(it);
    pthread_mutex_lock(&b->mutex);
    lru_bump_entry *be = (lru_bump_entry *) bipbuf_request(b->buf, sizeof(lru_bump_entry));
    if (be != NULL) {
        be->it = it;
        be->hv = hv;
        if (bipbuf_push(b->buf, sizeof(lru_bump_entry)) == 0) {
            ret = false;
            b->dropped++;
        }
    } else {
        ret = false;
        b->dropped++;
    }
    if (!ret) {
        refcount_decr(it);
    }
    pthread_mutex_unlock(&b->mutex);
    return ret;
}

/* TODO: Might be worth a micro-optimization of having bump buffers link
 * themselves back into the central queue when queue goes from zero to
 * non-zero, then remove from list if zero more than N times.
 * If very few hits on cold this would avoid extra memory barriers from LRU
 * maintainer thread. If many hits, they'll just stay in the list.
 */
static bool lru_maintainer_bumps(void) {
    lru_bump_buf *b;
    lru_bump_entry *be;
    unsigned int size;
    unsigned int todo;
    bool bumped = false;
    pthread_mutex_lock(&bump_buf_lock);
    for (b = bump_buf_head; b != NULL; b=b->next) {
        pthread_mutex_lock(&b->mutex);
        be = (lru_bump_entry *) bipbuf_peek_all(b->buf, &size);
        pthread_mutex_unlock(&b->mutex);

        if (be == NULL) {
            continue;
        }
        todo = size;
        bumped = true;

        while (todo) {
            item_lock(be->hv);
            do_item_update(be->it);
            do_item_remove(be->it);
            item_unlock(be->hv);
            be++;
            todo -= sizeof(lru_bump_entry);
        }

        pthread_mutex_lock(&b->mutex);
        be = (lru_bump_entry *) bipbuf_poll(b->buf, size);
        pthread_mutex_unlock(&b->mutex);
    }
    pthread_mutex_unlock(&bump_buf_lock);
    return bumped;
}

static uint64_t lru_total_bumps_dropped(void) {
    uint64_t total = 0;
    lru_bump_buf *b;
    pthread_mutex_lock(&bump_buf_lock);
    for (b = bump_buf_head; b != NULL; b=b->next) {
        pthread_mutex_lock(&b->mutex);
        total += b->dropped;
        pthread_mutex_unlock(&b->mutex);
    }
    pthread_mutex_unlock(&bump_buf_lock);
    return total;
}

/* Loop up to N times:
 * If too many items are in HOT_LRU, push to COLD_LRU
 * If too many items are in WARM_LRU, push to COLD_LRU
 * If too many items are in COLD_LRU, poke COLD_LRU tail
 * 1000 loops with 1ms min sleep gives us under 1m items shifted/sec. The
 * locks can't handle much more than that. Leaving a TODO for how to
 * autoadjust in the future.
 */
static int lru_maintainer_juggle(const int slabs_clsid) {
    int i;
    int did_moves = 0;
    uint64_t total_bytes = 0;
    unsigned int chunks_perslab = 0;
    //unsigned int chunks_free = 0;
    /* TODO: if free_chunks below high watermark, increase aggressiveness */
    slabs_available_chunks(slabs_clsid, NULL,
            &total_bytes, &chunks_perslab);
    if (settings.temp_lru) {
        /* Only looking for reclaims. Run before we size the LRU. */
        for (i = 0; i < 500; i++) {
            if (lru_pull_tail(slabs_clsid, TEMP_LRU, 0, 0, 0, NULL) <= 0) {
                break;
            } else {
                did_moves++;
            }
        }
        total_bytes -= temp_lru_size(slabs_clsid);
    }

    rel_time_t cold_age = 0;
    rel_time_t hot_age = 0;
    rel_time_t warm_age = 0;
    /* If LRU is in flat mode, force items to drain into COLD via max age */
    if (settings.lru_segmented) {
        pthread_mutex_lock(&lru_locks[slabs_clsid|COLD_LRU]);
        if (tails[slabs_clsid|COLD_LRU]) {
            cold_age = current_time - tails[slabs_clsid|COLD_LRU]->time;
        }
        pthread_mutex_unlock(&lru_locks[slabs_clsid|COLD_LRU]);
        hot_age = cold_age * settings.hot_max_factor;
        warm_age = cold_age * settings.warm_max_factor;
    }

    /* Juggle HOT/WARM up to N times */
    for (i = 0; i < 500; i++) {
        int do_more = 0;
        if (lru_pull_tail(slabs_clsid, HOT_LRU, total_bytes, LRU_PULL_CRAWL_BLOCKS, hot_age, NULL) ||
            lru_pull_tail(slabs_clsid, WARM_LRU, total_bytes, LRU_PULL_CRAWL_BLOCKS, warm_age, NULL)) {
            do_more++;
        }
        if (settings.lru_segmented) {
            do_more += lru_pull_tail(slabs_clsid, COLD_LRU, total_bytes, LRU_PULL_CRAWL_BLOCKS, 0, NULL);
        }
        if (do_more == 0)
            break;
        did_moves++;
    }
    return did_moves;
}

/* Will crawl all slab classes a minimum of once per hour */
#define MAX_MAINTCRAWL_WAIT 60 * 60

/* Hoping user input will improve this function. This is all a wild guess.
 * Operation: Kicks crawler for each slab id. Crawlers take some statistics as
 * to items with nonzero expirations. It then buckets how many items will
 * expire per minute for the next hour.
 * This function checks the results of a run, and if it things more than 1% of
 * expirable objects are ready to go, kick the crawler again to reap.
 * It will also kick the crawler once per minute regardless, waiting a minute
 * longer for each time it has no work to do, up to an hour wait time.
 * The latter is to avoid newly started daemons from waiting too long before
 * retrying a crawl.
 */
static void lru_maintainer_crawler_check(struct crawler_expired_data *cdata, logger *l) {
    int i;
    static rel_time_t next_crawls[POWER_LARGEST];
    static rel_time_t next_crawl_wait[POWER_LARGEST];
    uint8_t todo[POWER_LARGEST];
    memset(todo, 0, sizeof(uint8_t) * POWER_LARGEST);
    bool do_run = false;
    unsigned int tocrawl_limit = 0;

    // TODO: If not segmented LRU, skip non-cold
    for (i = POWER_SMALLEST; i < POWER_LARGEST; i++) {
        crawlerstats_t *s = &cdata->crawlerstats[i];
        /* We've not successfully kicked off a crawl yet. */
        if (s->run_complete) {
            char *lru_name = "na";
            pthread_mutex_lock(&cdata->lock);
            int x;
            /* Should we crawl again? */
            uint64_t possible_reclaims = s->seen - s->noexp;
            uint64_t available_reclaims = 0;
            /* Need to think we can free at least 1% of the items before
             * crawling. */
            /* FIXME: Configurable? */
            uint64_t low_watermark = (possible_reclaims / 100) + 1;
            rel_time_t since_run = current_time - s->end_time;
            /* Don't bother if the payoff is too low. */
            for (x = 0; x < 60; x++) {
                available_reclaims += s->histo[x];
                if (available_reclaims > low_watermark) {
                    if (next_crawl_wait[i] < (x * 60)) {
                        next_crawl_wait[i] += 60;
                    } else if (next_crawl_wait[i] >= 60) {
                        next_crawl_wait[i] -= 60;
                    }
                    break;
                }
            }

            if (available_reclaims == 0) {
                next_crawl_wait[i] += 60;
            }

            if (next_crawl_wait[i] > MAX_MAINTCRAWL_WAIT) {
                next_crawl_wait[i] = MAX_MAINTCRAWL_WAIT;
            }

            next_crawls[i] = current_time + next_crawl_wait[i] + 5;
            switch (GET_LRU(i)) {
                case HOT_LRU:
                    lru_name = "hot";
                    break;
                case WARM_LRU:
                    lru_name = "warm";
                    break;
                case COLD_LRU:
                    lru_name = "cold";
                    break;
                case TEMP_LRU:
                    lru_name = "temp";
                    break;
            }
            LOGGER_LOG(l, LOG_SYSEVENTS, LOGGER_CRAWLER_STATUS, NULL,
                    CLEAR_LRU(i),
                    lru_name,
                    (unsigned long long)low_watermark,
                    (unsigned long long)available_reclaims,
                    (unsigned int)since_run,
                    next_crawls[i] - current_time,
                    s->end_time - s->start_time,
                    s->seen,
                    s->reclaimed);
            // Got our calculation, avoid running until next actual run.
            s->run_complete = false;
            pthread_mutex_unlock(&cdata->lock);
        }
        if (current_time > next_crawls[i]) {
            pthread_mutex_lock(&lru_locks[i]);
            if (sizes[i] > tocrawl_limit) {
                tocrawl_limit = sizes[i];
            }
            pthread_mutex_unlock(&lru_locks[i]);
            todo[i] = 1;
            do_run = true;
            next_crawls[i] = current_time + 5; // minimum retry wait.
        }
    }
    if (do_run) {
        if (settings.lru_crawler_tocrawl && settings.lru_crawler_tocrawl < tocrawl_limit) {
            tocrawl_limit = settings.lru_crawler_tocrawl;
        }
        lru_crawler_start(todo, tocrawl_limit, CRAWLER_AUTOEXPIRE, cdata, NULL, 0);
    }
}

static pthread_t lru_maintainer_tid;

#define MAX_LRU_MAINTAINER_SLEEP 1000000
#define MIN_LRU_MAINTAINER_SLEEP 1000

static void *lru_maintainer_thread(void *arg) {
    int i;
    useconds_t to_sleep = MIN_LRU_MAINTAINER_SLEEP;
    useconds_t last_sleep = MIN_LRU_MAINTAINER_SLEEP;
    rel_time_t last_crawler_check = 0;
    rel_time_t last_automove_check = 0;
    useconds_t next_juggles[MAX_NUMBER_OF_SLAB_CLASSES] = {0};
    useconds_t backoff_juggles[MAX_NUMBER_OF_SLAB_CLASSES] = {0};
    struct crawler_expired_data *cdata =
        calloc(1, sizeof(struct crawler_expired_data));
    if (cdata == NULL) {
        fprintf(stderr, "Failed to allocate crawler data for LRU maintainer thread\n");
        abort();
    }
    pthread_mutex_init(&cdata->lock, NULL);
    cdata->crawl_complete = true; // kick off the crawler.
    logger *l = logger_create();
    if (l == NULL) {
        fprintf(stderr, "Failed to allocate logger for LRU maintainer thread\n");
        abort();
    }

    double last_ratio = settings.slab_automove_ratio;
    void *am = slab_automove_init(settings.slab_automove_window,
            settings.slab_automove_ratio);

    pthread_mutex_lock(&lru_maintainer_lock);
    if (settings.verbose > 2)
        fprintf(stderr, "Starting LRU maintainer background thread\n");
    while (do_run_lru_maintainer_thread) {
        pthread_mutex_unlock(&lru_maintainer_lock);
        if (to_sleep)
            usleep(to_sleep);
        pthread_mutex_lock(&lru_maintainer_lock);
        /* A sleep of zero counts as a minimum of a 1ms wait */
        last_sleep = to_sleep > 1000 ? to_sleep : 1000;
        to_sleep = MAX_LRU_MAINTAINER_SLEEP;

        STATS_LOCK();
        stats.lru_maintainer_juggles++;
        STATS_UNLOCK();

        /* Each slab class gets its own sleep to avoid hammering locks */
        for (i = POWER_SMALLEST; i < MAX_NUMBER_OF_SLAB_CLASSES; i++) {
            next_juggles[i] = next_juggles[i] > last_sleep ? next_juggles[i] - last_sleep : 0;

            if (next_juggles[i] > 0) {
                // Sleep the thread just for the minimum amount (or not at all)
                if (next_juggles[i] < to_sleep)
                    to_sleep = next_juggles[i];
                continue;
            }

            int did_moves = lru_maintainer_juggle(i);
            if (did_moves == 0) {
                if (backoff_juggles[i] != 0) {
                    backoff_juggles[i] += backoff_juggles[i] / 8;
                } else {
                    backoff_juggles[i] = MIN_LRU_MAINTAINER_SLEEP;
                }
                if (backoff_juggles[i] > MAX_LRU_MAINTAINER_SLEEP)
                    backoff_juggles[i] = MAX_LRU_MAINTAINER_SLEEP;
            } else if (backoff_juggles[i] > 0) {
                backoff_juggles[i] /= 2;
                if (backoff_juggles[i] < MIN_LRU_MAINTAINER_SLEEP) {
                    backoff_juggles[i] = 0;
                }
            }
            next_juggles[i] = backoff_juggles[i];
            if (next_juggles[i] < to_sleep)
                to_sleep = next_juggles[i];
        }

        /* Minimize the sleep if we had async LRU bumps to process */
        if (settings.lru_segmented && lru_maintainer_bumps() && to_sleep > 1000) {
            to_sleep = 1000;
        }

        /* Once per second at most */
        if (settings.lru_crawler && last_crawler_check != current_time) {
            lru_maintainer_crawler_check(cdata, l);
            last_crawler_check = current_time;
        }

        if (settings.slab_automove == 1 && last_automove_check != current_time) {
            if (last_ratio != settings.slab_automove_ratio) {
                slab_automove_free(am);
                am = slab_automove_init(settings.slab_automove_window,
                        settings.slab_automove_ratio);
                last_ratio = settings.slab_automove_ratio;
            }
            int src, dst;
            slab_automove_run(am, &src, &dst);
            if (src != -1 && dst != -1) {
                slabs_reassign(src, dst);
                LOGGER_LOG(l, LOG_SYSEVENTS, LOGGER_SLAB_MOVE, NULL,
                        src, dst);
            }
            // dst == 0 means reclaim to global pool, be more aggressive
            if (dst != 0) {
                last_automove_check = current_time;
            } else if (dst == 0) {
                // also ensure we minimize the thread sleep
                to_sleep = 1000;
            }
        }
    }
    pthread_mutex_unlock(&lru_maintainer_lock);
    slab_automove_free(am);
    // LRU crawler *must* be stopped.
    free(cdata);
    if (settings.verbose > 2)
        fprintf(stderr, "LRU maintainer thread stopping\n");

    return NULL;
}

int stop_lru_maintainer_thread(void) {
    int ret;
    pthread_mutex_lock(&lru_maintainer_lock);
    /* LRU thread is a sleep loop, will die on its own */
    do_run_lru_maintainer_thread = 0;
    pthread_mutex_unlock(&lru_maintainer_lock);
    if ((ret = pthread_join(lru_maintainer_tid, NULL)) != 0) {
        fprintf(stderr, "Failed to stop LRU maintainer thread: %s\n", strerror(ret));
        return -1;
    }
    settings.lru_maintainer_thread = false;
    return 0;
}

int start_lru_maintainer_thread(void *arg) {
    int ret;

    pthread_mutex_lock(&lru_maintainer_lock);
    do_run_lru_maintainer_thread = 1;
    settings.lru_maintainer_thread = true;
    if ((ret = pthread_create(&lru_maintainer_tid, NULL,
        lru_maintainer_thread, arg)) != 0) {
        fprintf(stderr, "Can't create LRU maintainer thread: %s\n",
            strerror(ret));
        pthread_mutex_unlock(&lru_maintainer_lock);
        return -1;
    }
    pthread_mutex_unlock(&lru_maintainer_lock);

    return 0;
}

/* If we hold this lock, crawler can't wake up or move */
void lru_maintainer_pause(void) {
    pthread_mutex_lock(&lru_maintainer_lock);
}

void lru_maintainer_resume(void) {
    pthread_mutex_unlock(&lru_maintainer_lock);
}

int init_lru_maintainer(void) {
    if (lru_maintainer_initialized == 0) {
        pthread_mutex_init(&lru_maintainer_lock, NULL);
        lru_maintainer_initialized = 1;
    }
    return 0;
}

/* Tail linkers and crawler for the LRU crawler. */
void do_item_linktail_q(item *it) { /* item is the new tail */
    item **head, **tail;
    assert(it->it_flags == 1);
    assert(it->nbytes == 0);

    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];
    //assert(*tail != 0);
    assert(it != *tail);
    assert((*head && *tail) || (*head == 0 && *tail == 0));
    it->prev = *tail;//将it插入到LRU的tail尾部 it的prev指向*tail
    it->next = 0;//it的next指向NULL
    if (it->prev) {//判断it的prev是否为NULL 即it是否为头部*head
        assert(it->prev->next == 0);
        it->prev->next = it;//it的prev不为NULL 则设置it的prev节点的next指向it
    }
    *tail = it;//*tail指向it
    if (*head == 0) *head = it;//判断*head是否为NULL 如果是 则*head指向it
    return;
}

void do_item_unlinktail_q(item *it) {
    item **head, **tail;
    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];

    if (*head == it) {//如果it是头部*head
        assert(it->prev == 0);
        *head = it->next;//设置*head指向it的next节点
    }
    if (*tail == it) {//如果it是尾部*tail
        assert(it->next == 0);
        *tail = it->prev;//设置*tail指向it的prev节点
    }
    assert(it->next != it);
    assert(it->prev != it);

    if (it->next) it->next->prev = it->prev;//it的next不为NULL 设置it的next节点的prev指向it的prev节点
    if (it->prev) it->prev->next = it->next;//it的prev不为NULL 设置it的prev节点的next指向it的next节点
    return;
}

/* This is too convoluted, but it's a difficult shuffle. Try to rewrite it
 * more clearly. */
item *do_item_crawl_q(item *it) {
    item **head, **tail;
    assert(it->it_flags == 1);
    assert(it->nbytes == 0);
    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];

    /* We've hit the head, pop off */
    if (it->prev == 0) {//如果it是头部head
        assert(*head == it);
        if (it->next) {//it的next不NULL 即it不是tail 即双链表不只it一个节点
            *head = it->next;//设置*head指向
            assert(it->next->prev == it);
            it->next->prev = 0;//it的next节点为head 则需设置该节点的prev指向NULL
        }
        return NULL; /* Done */ //it是头部head就会返回NULL
    }

    /* Swing ourselves in front of the next item */
    /* NB: If there is a prev, we can't be the head */
    assert(it->prev != it);
    if (it->prev) {//it不为NULL 即不是head
        if (*head == it->prev) {//如果it的pre是head
            /* Prev was the head, now we're the head */
            *head = it;//head指向it
        }
        if (*tail == it) {//如果it是尾部tail
            /* We are the tail, now they are the tail */
            *tail = it->prev;//tail指向it的prev
        }
        assert(it->next != it);
        if (it->next) {//如果it的next不为NULL
            assert(it->prev->next == it);
            it->prev->next = it->next;//设置it的prev节点的next指向
            it->next->prev = it->prev;//设置it的next节点的prev指向
        } else {
            /* Tail. Move this above? */
            it->prev->next = 0;//it是tail 则it的prev节点next指向设置为NULL
        }
        /* prev->prev's next is it->prev */
        it->next = it->prev;//重新设置it的next和prev指向 完成it向双两边prev方向移动 it的next指向it的prev节点（双链表）
        it->prev = it->next->prev;//it的prev指向it的next的prev节点（也就是it原先的prev->prev 且注意原先的it->prev是不为NULL）
        it->next->prev = it;//设置it原先prev节点的prev指向it 设置it的next节点的prev指向it（双链表） 
        /* New it->prev now, if we're not at the head. */
        if (it->prev) {//判断it向prev方向移动后 it的prev是否为NULL 即it是否在head位置
            it->prev->next = it;//it不在head位置 则需设置it的prev节点的next指向it（双链表）
        }
    }
    assert(it->next != it);
    assert(it->prev != it);

    return it->next; /* success */ //返回it的next节点 注该节点是it移动之前的prev节点
}
