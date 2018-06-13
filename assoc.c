/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
/*
 * Hash table
 *
 * The hash function used here is by Bob Jenkins, 1996:
 *    <http://burtleburtle.net/bob/hash/doobs.html>
 *       "By Bob Jenkins, 1996.  bob_jenkins@burtleburtle.net.
 *       You may use this code any way you wish, private, educational,
 *       or commercial.  It's free."
 *
 * The rest of the file is licensed under the BSD license.  See LICENSE.
 */

#include "memcached.h"
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/resource.h>
#include <signal.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <errno.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <pthread.h>

static pthread_cond_t maintenance_cond = PTHREAD_COND_INITIALIZER;
static pthread_mutex_t maintenance_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t hash_items_counter_lock = PTHREAD_MUTEX_INITIALIZER;

typedef  unsigned long  int  ub4;   /* unsigned 4-byte quantities */
typedef  unsigned       char ub1;   /* unsigned 1-byte quantities */

/* how many powers of 2's worth of buckets we use */
unsigned int hashpower = HASHPOWER_DEFAULT;

#define hashsize(n) ((ub4)1<<(n))
#define hashmask(n) (hashsize(n)-1)

/* Main hash table. This is where we look except during expansion. */
static item** primary_hashtable = 0;

/*
 * Previous hash table. During expansion, we look here for keys that haven't
 * been moved over to the primary yet.
 */
static item** old_hashtable = 0;

/* Number of items in the hash table. */
static unsigned int hash_items = 0;

/* Flag: Are we in the middle of expanding now? */
static bool expanding = false;
static bool started_expanding = false;

/*
 * During expansion we migrate values with bucket granularity; this is how
 * far we've gotten so far. Ranges from 0 .. hashsize(hashpower - 1) - 1.
 */
static unsigned int expand_bucket = 0;

void assoc_init(const int hashtable_init) {//hash表初始化
    if (hashtable_init) {
        hashpower = hashtable_init;
    }
    primary_hashtable = calloc(hashsize(hashpower), sizeof(void *));//hash表 其中槽数为hashsize(hashpower)
    if (! primary_hashtable) {
        fprintf(stderr, "Failed to init hashtable.\n");
        exit(EXIT_FAILURE);
    }
    STATS_LOCK();
    stats_state.hash_power_level = hashpower;
    stats_state.hash_bytes = hashsize(hashpower) * sizeof(void *);
    STATS_UNLOCK();
}

item *assoc_find(const char *key, const size_t nkey, const uint32_t hv) {//由于hash值只能确定是在hash表中的哪个桶（bucket） 但一个桶里面是有一条冲突链的 此时需要用到具体的键值遍历并一一比较冲突链上的所有节点 虽然key是以‘\0’结尾的字符串 但调用strlen还是很耗时（需要遍历键值字符串） 所以需要另外一个参数nkey指明这个key的长度
    item *it;
    unsigned int oldbucket;
    //找出这个key是属于哪个桶 
    if (expanding &&
        (oldbucket = (hv & hashmask(hashpower - 1))) >= expand_bucket)//找出槽位hv & hashmask(hashpower - 1) //如果数据正在迁移 且 插入的数据在旧hash表中的桶下标大于正在进行数据扩展的桶下标
    {
        it = old_hashtable[oldbucket];
    } else {
        it = primary_hashtable[hv & hashmask(hashpower)];//primary hash表 计算出槽位hv&hashmask(hashpower)
    }

    item *ret = NULL;
    int depth = 0;
    while (it) {//遍历key所在桶的冲突链 找出key具体位置
        if ((nkey == it->nkey) && (memcmp(key, ITEM_key(it), nkey) == 0)) {//判断是否找到 先比较key的大小 然后比较key字符串是否相等 memcmp函数返回0表示比较的两个字符串相等
            ret = it;
            break;
        }
        it = it->h_next;//it指向list中的h_next  memcacahed中是使用链地址方法解决冲突
        ++depth;//
    }
    MEMCACHED_ASSOC_FIND(key, nkey, depth);
    return ret;
}

/* returns the address of the item pointer before the key.  if *item == 0,
   the item wasn't found */

static item** _hashitem_before (const char *key, const size_t nkey, const uint32_t hv) {//查找item 返回前驱节点的h_next成员地址 如果查找失败那么就返回冲突链中最后一个节点的h_next成员地址。因为最后一个节点的h_next的值为NULL。通过对返回值使用*运算符即可以知道有查找成功
    item **pos;
    unsigned int oldbucket;

    if (expanding &&
        (oldbucket = (hv & hashmask(hashpower - 1))) >= expand_bucket)//old_hashtable  //同样面临在进行数据扩展时进行查询 //如果数据正在迁移 且 插入的数据在旧hash表中的桶下标大于正在进行数据扩展的桶下标
    {
        pos = &old_hashtable[oldbucket];
    } else {
        pos = &primary_hashtable[hv & hashmask(hashpower)];//primary_hashtable
    }
    //遍历冲突链中查找item
    while (*pos && ((nkey != (*pos)->nkey) || memcmp(key, ITEM_key(*pos), nkey))) {//*pos非NULL 且 (key的字符创长度不相等 后 key字符长度相等但比较的两个字符创不相等)
        pos = &(*pos)->h_next;//pos为前驱的h_next成员的地址 而前驱的h_next指向的就是item
    }
    return pos;//*pos就可以知道有没查找成功 如果*pos等于NULL则查找失败 否则查找成功
}

/* grows the hashtable to the next power of 2. */
static void assoc_expand(void) {//扩展hash表
    old_hashtable = primary_hashtable;//将primary_hashtable赋值为old_hashtable

    primary_hashtable = calloc(hashsize(hashpower + 1), sizeof(void *));//重新申请primary_hashtable 其中大小为之前的2倍hashsize(hashpower + 1)
    if (primary_hashtable) {//扩展申请内存成功
        if (settings.verbose > 1)
            fprintf(stderr, "Hash table expansion starting\n");
        hashpower++;//hashpower自加1
        expanding = true;//设置expanding为true 即hash表进行了扩展
        expand_bucket = 0;//
        STATS_LOCK();
        stats_state.hash_power_level = hashpower;
        stats_state.hash_bytes += hashsize(hashpower) * sizeof(void *);
        stats_state.hash_is_expanding = true;
        STATS_UNLOCK();
    } else {
        primary_hashtable = old_hashtable;//如果扩展申请内存失败 将使用原先的内存
        /* Bad news, but we can keep running. */
    }
}

static void assoc_start_expand(void) {//assoc_insert函数会调用本函数 当item数量到了hash表表长的1.5倍才会调用的
    if (started_expanding)
        return;

    started_expanding = true;
    pthread_cond_signal(&maintenance_cond);//条件变量 通知数据迁移线程
}

/* Note: this isn't an assoc_update.  The key must not already exist to call this */
int assoc_insert(item *it, const uint32_t hv) {//insert操作  hv为item键值的hash值  //同时需要注意的是 memcached可能在迁移的同时进行插入insert 这时memcached的具体处理
    unsigned int oldbucket;

//    assert(assoc_find(ITEM_key(it), it->nkey) == 0);  /* shouldn't have duplicately named things defined */

    if (expanding &&
        (oldbucket = (hv & hashmask(hashpower - 1))) >= expand_bucket)//如果数据正在迁移 且 插入的数据在旧hash表中的桶下标大于正在进行数据扩展的桶下标 那就插入到旧hash表桶中
    {
        it->h_next = old_hashtable[oldbucket];//在头部插入 即插入item的h_next指向桶头部
        old_hashtable[oldbucket] = it;//桶头部指向刚插入的item
    } else {//否则就插入到primary_hashtable中
        it->h_next = primary_hashtable[hv & hashmask(hashpower)];//在头部插入
        primary_hashtable[hv & hashmask(hashpower)] = it;
    }

    pthread_mutex_lock(&hash_items_counter_lock);
    hash_items++;//hash表中的item个数加1
    if (! expanding && hash_items > (hashsize(hashpower) * 3) / 2 &&
          hashpower < HASHPOWER_MAX) {//需要扩展 需要进行数据迁移
        assoc_start_expand();
    }
    pthread_mutex_unlock(&hash_items_counter_lock);

    MEMCACHED_ASSOC_INSERT(ITEM_key(it), it->nkey, hash_items);
    return 1;
}

void assoc_delete(const char *key, const size_t nkey, const uint32_t hv) {//delete操作 key为键 nkey为键的长度 hv为key的hash值
    item **before = _hashitem_before(key, nkey, hv);//找到前驱节点的h_next成员地址

    if (*before) {//查找成功
        item *nxt;
        pthread_mutex_lock(&hash_items_counter_lock);//lock
        hash_items--;//hash中item个数减1
        pthread_mutex_unlock(&hash_items_counter_lock);
        /* The DTrace probe cannot be triggered as the last instruction
         * due to possible tail-optimization by the compiler
         */
        MEMCACHED_ASSOC_DELETE(key, nkey, hash_items);
        nxt = (*before)->h_next;//nxt就是要删除的item的下一个itme  因为before是一个二级指针 其值为所查找item的前驱item的h_next成员地址 所以*before指向的是所查找的item 因为before是一个二级指针 所以*before作为左值时 可以给h_next成员变量赋值 所以(*before)->h_next就是要找的item的下一个item
        (*before)->h_next = 0;//要删除item的h_next成员设置为0   /* probably pointless, but whatever. */
        *before = nxt;//要删除item的前驱的h_next成员指向nxt 到此 item已经移除
        return;
    }
    /* Note:  we never actually get here.  the callers don't delete things
       they can't find. */
    assert(*before != 0);
}


static volatile int do_run_maintenance_thread = 1;

#define DEFAULT_HASH_BULK_MOVE 1
int hash_bulk_move = DEFAULT_HASH_BULK_MOVE;

static void *assoc_maintenance_thread(void *arg) {//数据迁移线程 main函数中启动

    mutex_lock(&maintenance_lock);//lock
    while (do_run_maintenance_thread) {//do_run_maintenance_thread是全局变量 初始值为1 在stop_assoc_maintenance_thread函数中会赋值0 终止数据迁移线程
        int ii = 0;

        /* There is only one expansion thread, so no need to global lock. */ //是有一个扩展线程不需要全局锁
        for (ii = 0; ii < hash_bulk_move && expanding; ++ii) {//注 expanding初始值为false hash_bulk_move是指多少个桶的item 默认是一个桶的item
            item *it, *next;
            unsigned int bucket;
            void *item_lock = NULL;

            /* bucket = hv & hashmask(hashpower) =>the bucket of hash table
             * is the lowest N bits of the hv, and the bucket of item_locks is
             *  also the lowest M bits of hv, and N is greater than M.
             *  So we can process expanding with only one item_lock. cool! */
            if ((item_lock = item_trylock(expand_bucket))) {//获取expand_bucket的锁  注在扩展函数assoc_expand中将expand_bucket设置为0 即表示从桶下标0开始进行数据迁移 item_trylock是在thread.c中定义 trylock(&item_locks[hv & hashmask(item_lock_hashpower)]) 尝试获取段锁
                    for (it = old_hashtable[expand_bucket]; NULL != it; it = next) {//遍历迁移桶下标为expand_bucket的冲突链所有的item
                        next = it->h_next;//next保留旧桶冲突链
                        bucket = hash(ITEM_key(it), it->nkey) & hashmask(hashpower);//计算item新桶下标 注hashpower已经在扩展函数assoc_expand中增加了1
                        it->h_next = primary_hashtable[bucket];//注item插入新的桶的头部
                        primary_hashtable[bucket] = it;//修改新桶的头部指向 指向刚迁移的item
                    }

                    old_hashtable[expand_bucket] = NULL;//旧桶expand_bucket已经迁移完成 将其设置为NULL

                    expand_bucket++;//旧桶下标加1 
                    if (expand_bucket == hashsize(hashpower - 1)) {//如果旧桶下标达到了旧桶数即旧hash表的桶数hashsize(hashpower - 1) 表示数据迁移完成
                        expanding = false;//设置expanding为false 表示数据迁移结束
                        free(old_hashtable);//释放旧hash表
                        STATS_LOCK();
                        stats_state.hash_bytes -= hashsize(hashpower - 1) * sizeof(void *);//设置state数据
                        stats_state.hash_is_expanding = false;
                        STATS_UNLOCK();
                        if (settings.verbose > 1)
                            fprintf(stderr, "Hash table expansion done\n");
                    }

            } else {//如果没有获得锁 旧sleep 10毫秒
                usleep(10*1000);
            }

            if (item_lock) {//释放锁
                item_trylock_unlock(item_lock);
                item_lock = NULL;
            }
        }

        if (!expanding) {//expanding初始值为false  expanding具体是在assoc_expand设置为true 以及数据迁移完成后expanding也将被设置为false
            /* We are done expanding.. just wait for next invocation */
            started_expanding = false;
            pthread_cond_wait(&maintenance_cond, &maintenance_lock);//等待 条件变量 maintenance_cond 迁移线程被创建后进入睡眠 当worker线程插入item后 发现需要扩展hash表就会调用assoc_start_expand函数唤醒这个迁移线程
            /* assoc_expand() swaps out the hash table entirely, so we need
             * all threads to not hold any references related to the hash
             * table while this happens.
             * This is instead of a more complex, possibly slower algorithm to
             * allow dynamic hash table expansion without causing significant
             * wait times.
             */
            pause_threads(PAUSE_ALL_THREADS);
            assoc_expand();//hash表进行扩展
            pause_threads(RESUME_ALL_THREADS);
        }
    }
    return NULL;
}

static pthread_t maintenance_tid;

int start_assoc_maintenance_thread() {//开启数据迁移线程
    int ret;
    char *env = getenv("MEMCACHED_HASH_BULK_MOVE");
    if (env != NULL) {
        hash_bulk_move = atoi(env);//hash_bulk_move是通过环境变量赋值 具体指明多少个桶的item
        if (hash_bulk_move == 0) {
            hash_bulk_move = DEFAULT_HASH_BULK_MOVE;
        }
    }
    pthread_mutex_init(&maintenance_lock, NULL);//init lock
    if ((ret = pthread_create(&maintenance_tid, NULL,
                              assoc_maintenance_thread, NULL)) != 0) {
        fprintf(stderr, "Can't create thread: %s\n", strerror(ret));
        return -1;
    }
    return 0;
}

void stop_assoc_maintenance_thread() {//终止数据迁移线程
    mutex_lock(&maintenance_lock);//lock
    do_run_maintenance_thread = 0;//设置do_run_maintenance_thread为0 则数据迁移线程将会推出while循环而终止
    pthread_cond_signal(&maintenance_cond);//cond_signal通知数据迁移线程 
    mutex_unlock(&maintenance_lock);//unlock

    /* Wait for the maintenance thread to stop */
    pthread_join(maintenance_tid, NULL);//等待数据迁移线程终止
}

