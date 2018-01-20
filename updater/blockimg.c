/*
 * Copyright (C) 2014 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <ctype.h>
#include <errno.h>
#include <dirent.h>
#include <fcntl.h>
#include <inttypes.h>
#include <pthread.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/ioctl.h>
#include <time.h>
#include <unistd.h>

#include "applypatch/applypatch.h"
#include "edify/expr.h"
#include "mincrypt/sha.h"
//Split individual transfer list commands into separate functions with unified parameters for clarity, and use a hash table to locate them during execution.
#include "minzip/Hash.h"
#include "updater.h"

#define BLOCKSIZE 4096

// Set this to 0 to interpret 'erase' transfers to mean do a
// BLKDISCARD ioctl (the normal behavior).  Set to 1 to interpret
// erase to mean fill the region with zeroes.
#define DEBUG_ERASE  0

#ifndef BLKDISCARD
#define BLKDISCARD _IO(0x12,119)
#endif

#define STASH_DIRECTORY_BASE "/cache/recovery"
#define STASH_DIRECTORY_MODE 0700
#define STASH_FILE_MODE 0600

char* PrintSha1(const uint8_t* digest);

typedef struct {
    int count;
    int size;
    int pos[0];
} RangeSet;

//在BlockImageUpdateFn中的调用情况为:  RangeSet* tgt = parse_range(word);
//这时word指向的是 30,32770,32825,32827,33307,65535,65536,65538,66018,98303,98304,98306,98361,98363,98843,131071,131072,131074,131554,162907,163840,163842,16///3897,163899,164379,196607,196608,196610,197090,215039,215040
static RangeSet* parse_range(char* text) {
    char* save;
    int num;
    //将text最前面的 block编号 个数30 给num
    num = strtol(strtok_r(text, ",", &save), NULL, 0);

    RangeSet* out = malloc(sizeof(RangeSet) + num * sizeof(int));
    if (out == NULL) {
        fprintf(stderr, "failed to allocate range of %lu bytes\n",
                sizeof(RangeSet) + num * sizeof(int));
        exit(1);
    }
    // 30个block编号,num=30,  两个block编号构成一个区间, 一共15个范围
    out->count = num / 2;
    out->size = 0;
    int i;
    for (i = 0; i < num; ++i) {
         //30个out->pos[i] 就保存的是每个block编号
        out->pos[i] = strtol(strtok_r(NULL, ",", &save), NULL, 0);
        if (i%2) {
             // i = 1, out->size = 0 - 32770 + 32825
            out->size += out->pos[i];
        } else {
            //i=0时,out->size = 0 - 32770
            out->size -= out->pos[i];
        }
    }
    //for循环执行完, out->size就= (32825 - 32770) + (33370 - 32827) + ..... 15个范围每个的右边减左边

    return out;
}

static int range_overlaps(RangeSet* r1, RangeSet* r2) {
    int i, j, r1_0, r1_1, r2_0, r2_1;

    if (!r1 || !r2) {
        return 0;
    }

    for (i = 0; i < r1->count; ++i) {
        r1_0 = r1->pos[i * 2];
        r1_1 = r1->pos[i * 2 + 1];

        for (j = 0; j < r2->count; ++j) {
            r2_0 = r2->pos[j * 2];
            r2_1 = r2->pos[j * 2 + 1];

            if (!(r2_0 > r1_1 || r1_0 > r2_1)) {
                return 1;
            }
        }
    }

    return 0;
}

// 读取文件描述符fd指向数据到data,读取大小为size.成功返回0,失败返回-1
static int read_all(int fd, uint8_t* data, size_t size) {
    size_t so_far = 0;
    while (so_far < size) {
        ssize_t r = read(fd, data+so_far, size-so_far);
        if (r < 0 && errno != EINTR) {
            fprintf(stderr, "read failed: %s\n", strerror(errno));
            return -1;
        } else {
            so_far += r;
        }
    }
    return 0;
}

// 将data指向的大小为size的数据写入fd,成功返回0,失败返回-1
static int write_all(int fd, const uint8_t* data, size_t size) {
    size_t written = 0;
    while (written < size) {
        ssize_t w = write(fd, data+written, size-written);
        if (w < 0 && errno != EINTR) {
            fprintf(stderr, "write failed: %s\n", strerror(errno));
            return -1;
        } else {
            written += w;
        }
    }

    if (fsync(fd) == -1) {
        fprintf(stderr, "fsync failed: %s\n", strerror(errno));
        return -1;
    }

    return 0;
}

// check_lseek函数用于设置写入的偏移量,定位写入位置
// 成功返回0,失败返回-1
static int check_lseek(int fd, off64_t offset, int whence) {
    while (true) {
        off64_t ret = lseek64(fd, offset, whence);
        if (ret < 0) {
            if (errno != EINTR) {
                fprintf(stderr, "lseek64 failed: %s\n", strerror(errno));
                return -1;
            }
        } else {
            break;
        }
    }
    return 0;
}

static void allocate(size_t size, uint8_t** buffer, size_t* buffer_alloc) {
    // if the buffer's big enough, reuse it.
    if (size <= *buffer_alloc) return;

    free(*buffer);

    *buffer = (uint8_t*) malloc(size);
    if (*buffer == NULL) {
        fprintf(stderr, "failed to allocate %zu bytes\n", size);
        exit(1);
    }
    *buffer_alloc = size;
}

typedef struct {
    int fd;
    RangeSet* tgt;
    int p_block;
    size_t p_remain;
} RangeSinkState;

// 在RangeSinkWrite中实现将system.new.data解压后的数据写入target的功能
// RangeSinkWrite 相对于函数FileSink和MemorySink,是将一个区间段数据写入闪存
// 1 在BlockImageUpdateFn中执行transfer.list中的imgdiff或bsdiff命令时,调用ApplyImagePatch或ApplyBSDiffPatch时传入的sink函数指针
// 2 receive_new_data中直接调用
// data -- 要写入的数据的起始地址
// size -- 要写入的数据大小
// token -- 
static ssize_t RangeSinkWrite(const uint8_t* data, ssize_t size, void* token) {
    RangeSinkState* rss = (RangeSinkState*) token;

    // 对于BlockImageUpdateFn中的调用,	RangeSinkState rss; rss.p_remain = (tgt->pos[1] - tgt->pos[0]) * BLOCKSIZE;
    // RangeSinkState的p_remain代表剩余要从内存写入闪存的数据大小
    if (rss->p_remain <= 0) {
        fprintf(stderr, "range sink write overrun");
        // 之前是exit(1); transfer list V3中检测到这种情况不推出,返回0
        return 0;
    }

    // written代表已经写入的数据的大小
    ssize_t written = 0;
    while (size > 0) {
        // write_now代表剩余要写入的大小
        size_t write_now = size;

        if (rss->p_remain < write_now) {
            write_now = rss->p_remain;
        }

        // 写入write_now大小的数据
        if (write_all(rss->fd, data, write_now) == -1) {
            break;
        }
        
 
        // 移动要写入的should地址
        data += write_now;
        size -= write_now;

        rss->p_remain -= write_now;
        // 写入完后已经写入数据大小written要加上write_now
        written += write_now;

        if (rss->p_remain == 0) {
            // move to the next block
            // RangeSinkState的p_block表示已写入的block区段的个数
            // 因此如果p_remain为0就说明一个区段内的block均已更新,这时p_block就要+1
            ++rss->p_block;
            // 如果p_block<总区段个数,就继续更新下一个block区间
            if (rss->p_block < rss->tgt->count) {
			    rss->p_remain = (rss->tgt->pos[rss->p_block * 2 + 1] -
							  rss->tgt->pos[rss->p_block * 2]) * BLOCKSIZE;

                // 调用check_lseek,将读写位置指向下一个block区间其实位置
 			    if (check_lseek(rss->fd, (off64_t)rss->tgt->pos[rss->p_block*2] * BLOCKSIZE,
 					    SEEK_SET) == -1) {
 				    break;
 			    }

            } else {
                // 说明已经更新完所有block区间, 返回已经写入的数据的大小
                // we can't write any more; return how many bytes have
                // been written so far.
                break;
            }
        }
    }

    return written;
}

// All of the data for all the 'new' transfers is contained in one
// file in the update package, concatenated together in the order in
// which transfers.list will need it.  We want to stream it out of the
// archive (it's compressed) without writing it to a temp file, but we
// can't write each section until it's that transfer's turn to go.
//
// To achieve this, we expand the new data from the archive in a
// background thread, and block that threads 'receive uncompressed
// data' function until the main thread has reached a point where we
// want some new data to be written.  We signal the background thread
// with the destination for the data and block the main thread,
// waiting for the background thread to complete writing that section.
// Then it signals the main thread to wake up and goes back to
// blocking waiting for a transfer.
//
// NewThreadInfo is the struct used to pass information back and forth
// between the two threads.  When the main thread wants some data
// written, it sets rss to the destination location and signals the
// condition.  When the background thread is done writing, it clears
// rss and signals the condition again.

typedef struct {
    ZipArchive* za;
    const ZipEntry* entry;

    RangeSinkState* rss;

    pthread_mutex_t mu;
    pthread_cond_t cv;
} NewThreadInfo;

// 相关调用顺序为:BlockImageUpdateFn--unzip_new_data--mzProcessZipEntryContents--processDeflatedEntry或processStoredEntry--receive_new_data
static bool receive_new_data(const unsigned char* data, int size, void* cookie) {
    NewThreadInfo* nti = (NewThreadInfo*) cookie;

    while (size > 0) {
        // Wait for nti->rss to be non-NULL, indicating some of this
        // data is wanted.
        // nti->rss在BlockImageUpdateFn开始为NULL,
        //            pthread_mutex_lock(&nti.mu);
        //            nti.rss = &rss;		               在解析system.transfer.list循环中如果遇见new命令,主线程就会在互斥锁中给nti->rss赋值
        //            pthread_cond_broadcast(&nti.cv);
        //            while (nti.rss) {  //在receive_new_data函数中在所有解压system.new.data的数据都写入完后将nti->rss=NULL, 在这之前主线程BlockImageUpdateFn一直阻塞
        //                pthread_cond_wait(&nti.cv, &nti.mu); 
        //            }
        //            pthread_mutex_unlock(&nti.mu);
        // nti的mu,cv都是线程相关的信号量, pthread_mutex_t mu;  pthread_cond_t cv; 
        pthread_mutex_lock(&nti->mu);
        //receive_new_data所在的后台线程执行到这里就一直等待主线程执行nti.rss = &rss;
        while (nti->rss == NULL) {
            pthread_cond_wait(&nti->cv, &nti->mu);
        }
        pthread_mutex_unlock(&nti->mu);

        //while跳出后说明主线程执行了nti.rss = &rss;  其中RangeSinkState rss;  rss.fd = fd;  rss.tgt = tgt;   rss.p_block = 0;  rss.p_remain = (tgt->pos[1] - tgt->pos[0]) * BLOCKSIZE;
        // At this point nti->rss is set, and we own it.  The main
        // thread is waiting for it to disappear from nti.
        ssize_t written = RangeSinkWrite(data, size, nti->rss);
        //RangeSinkWrite返回写入数据多少,因此写入地址data要加上返回值written,要写入多少size要减返回值
        data += written;
        size -= written;

        if (nti->rss->p_block == nti->rss->tgt->count) {
            // we have written all the bytes desired by this rss.

            pthread_mutex_lock(&nti->mu);
            //解压system.new.data的数据都写入完后将nti->rss=NULL
            nti->rss = NULL;
            pthread_cond_broadcast(&nti->cv);
            pthread_mutex_unlock(&nti->mu);
        }
    }

    return true;
}

// 在BlockImageUpdateFn中创建了一个线程new_data_thread,执行函数unzip_new_data, 来完成对system.new.dat文件的处理:pthread_create(&new_data_thread, &attr, unzip_new_data, &nti);
// 传给unzip_new_data的参数nti取值为:
// NewThreadInfo nti;
// nti.za = za;  // za代表ota zip包, ZipArchive* za = ((UpdaterInfo*)(state->cookie))->package_zip;
// nti.entry = new_entry; // 这里就将ota zip包中的system.new.dat传给了nti.entry, const ZipEntry* new_entry = mzFindZipEntry(za, new_data_fn->data);
// nti.rss = NULL;  // 先将rss标记置空
// pthread_mutex_init(&nti.mu, NULL); // 互斥锁的初始化
// pthread_cond_init(&nti.cv, NULL); // 创建一个条件变量，cv就是condition value的意思
static void* unzip_new_data(void* cookie) {
    NewThreadInfo* nti = (NewThreadInfo*) cookie;
    // unzip_new_data函数主要调用mzProcessZipEntryContents完成对system.new.data文件的解压
    mzProcessZipEntryContents(nti->za, nti->entry, receive_new_data, nti);
    return NULL;
}

//block_image_update("/dev/block/bootdevice/by-name/system", package_extract_file("system.transfer.list"), "system.new.dat", "system.patch.dat");
// args:
//    - block device (or file) to modify in-place
//    - transfer list (blob)
//    - new data stream (filename within package.zip)
//    - patch stream (filename within package.zip, must be uncompressed)

Value* BlockImageUpdateFn(const char* name, State* state, int argc, Expr* argv[]) {
    Value* blockdev_filename;
    Value* transfer_list_value;
    char* transfer_list = NULL;
    Value* new_data_fn;
    Value* patch_data_fn;
    bool success = false;

	//ReadValueArgs取得脚本中的/dev/block/bootdevice/by-name/system，package_extract_file("system.transfer.list"),system.new.dat", "system.patch.dat"这四个参数，赋值给blockdev_filename ，transfer_list_value， new_data_fn，patch_data_fn
	// 因为block_image_update中有类似package_extract_file("system.transfer.list")这种还需要执行才能得到返回值的函数
	// 在ReadValueArgs中利用va_list等C语言的可变参数宏，将block_image_update的四个输入参数"/dev/block/bootdevice/by-name/system", package_extract_file("system.transfer.list"), "system.new.dat", "system.patch.dat"，分别赋值给blockdev_filename，transfer_list_value，new_data_fn，patch_data_fn
    if (ReadValueArgs(state, argv, 4, &blockdev_filename, &transfer_list_value,
                      &new_data_fn, &patch_data_fn) < 0) {
        return NULL;
    }

    if (blockdev_filename->type != VAL_STRING) {
	//在BlockImageUpdateFn函数中name就是block_image_update,这个错误log的意思就是block_image_update的blockdev_filename参数必须是string类型
        ErrorAbort(state, "blockdev_filename argument to %s must be string", name);
        goto done;
    }
	//在package_extract_file("system.transfer.list"),中将type设为了VAL_BLOB
	//BLOB (binary large object)，二进制大对象，是一个可以存储二进制文件的容器 //BLOB是一个大文件，典型的BLOB是一张图片或一个声音文件，由于它们的尺寸，必须使用特殊的方式来处理（例如：上传、下载或者存放到一个数据库）
    if (transfer_list_value->type != VAL_BLOB) {
        ErrorAbort(state, "transfer_list argument to %s must be blob", name);
        goto done;
    }
    if (new_data_fn->type != VAL_STRING) {
        ErrorAbort(state, "new_data_fn argument to %s must be string", name);
        goto done;
    }
    if (patch_data_fn->type != VAL_STRING) {
        ErrorAbort(state, "patch_data_fn argument to %s must be string", name);
        goto done;
    }

	// 这里的ui是updater info的含义，而不是user interface
    UpdaterInfo* ui = (UpdaterInfo*)(state->cookie);
    // 升级时updater子进程通过cmd_pipe将progress进度传给recovery进程
    FILE* cmd_pipe = ui->cmd_pipe;

	// za这时就代表zip格式的整个ota包
    ZipArchive* za = ((UpdaterInfo*)(state->cookie))->package_zip;

	//patch_data_fn->data指向的是“system.patch.dat”这段字符串，而不是 system.patch.dat这个文件的内容，
    //因此patch_entry就代表内存中的zip安装包中的system.patch.dat这一项
    const ZipEntry* patch_entry = mzFindZipEntry(za, patch_data_fn->data);
    if (patch_entry == NULL) {
        ErrorAbort(state, "%s(): no file \"%s\" in package", name, patch_data_fn->data);
        goto done;
    }

	//计算出patch_entry的起始地址，因为注释中说patch stream must be uncompressed
	//patch_start在下面循环中执行bsdiff或imgdiff命令中会用到
    uint8_t* patch_start = ((UpdaterInfo*)(state->cookie))->package_zip_addr +
        mzGetZipEntryOffset(patch_entry);

	//new_data_fn->data指向的数据是“system.new.dat”，而不是system.new.dat这个文件的内容
	//new_entry就代表内存中的zip安装包中的system.new.dat这一项
    const ZipEntry* new_entry = mzFindZipEntry(za, new_data_fn->data);
    if (new_entry == NULL) {
        ErrorAbort(state, "%s(): no file \"%s\" in package", name, new_data_fn->data);
        goto done;
    }

    // The transfer list is a text file containing commands to
    // transfer data from one place to another on the target
    // partition.  We parse it and execute the commands in order:
    //
    //    zero [rangeset]
    //      - fill the indicated blocks with zeros
    //
    //    new [rangeset]
    //      - fill the blocks with data read from the new_data file
    //
    //    bsdiff patchstart patchlen [src rangeset] [tgt rangeset]
    //    imgdiff patchstart patchlen [src rangeset] [tgt rangeset]
    //      - read the source blocks, apply a patch, write result to
    //        target blocks.  bsdiff or imgdiff specifies the type of
    //        patch.
    //
    //    move [src rangeset] [tgt rangeset]
    //      - copy data from source blocks to target blocks (no patch
    //        needed; rangesets are the same size)
    //
    //    erase [rangeset]
    //      - mark the given blocks as empty
    //
    // The creator of the transfer list will guarantee that no block
    // is read (ie, used as the source for a patch or move) after it
    // has been written.
    //
    // Within one command the source and target ranges may overlap so
    // in general we need to read the entire source into memory before
    // writing anything to the target blocks.
    //
    // All the patch data is concatenated into one patch_data file in
    // the update package.  It must be stored uncompressed because we
    // memory-map it in directly from the archive.  (Since patches are
    // already compressed, we lose very little by not compressing
    // their concatenation.)

// we expand the new data from the archive in a
// background thread, and block that threads 'receive uncompressed
// data' function until the main thread has reached a point where we
// want some new data to be written.  We signal the background thread
// with the destination for the data and block the main thread,
// waiting for the background thread to complete writing that section.
// Then it signals the main thread to wake up and goes back to
// blocking waiting for a transfer.
// NewThreadInfo is the struct used to pass information back and forth
// between the two threads.  When the main thread wants some data
// written, it sets rss to the destination location and signals the
// condition.  When the background thread is done writing, it clears
// rss and signals the condition again.
    pthread_t new_data_thread;
    NewThreadInfo nti;
    // nti.za就代表整个zip格式的ota包
    nti.za = za;
	// 这里就将ota zip包中的system.new.dat传给了nti.entry
    nti.entry = new_entry;
	//先将rss标记置空
    nti.rss = NULL;
	//互斥锁的初始化
    pthread_mutex_init(&nti.mu, NULL);
	//创建一个条件变量，cv就是condition value的意思
	 //extern int pthread_cond_init __P ((pthread_cond_t *__cond,__const pthread_condattr_t *__cond_attr)); 其中cond是一个指向结构pthread_cond_t的指针，cond_attr是一个指向结构pthread_condattr_t的指 针。结构 pthread_condattr_t是条件变量的属性结构，和互斥锁一样我 们可以用它来设置条件变量是进程内可用还是进程间可用，默认值是 PTHREAD_ PROCESS_PRIVATE，即此条件变量被同一进程内的各个线程使用
    pthread_cond_init(&nti.cv, NULL);

	//线程具有属性,用pthread_attr_t表示,在对该结构进行处理之前必须进行初始化，我们用pthread_attr_init函数对其初始化，用pthread_attr_destroy对其去除初始化
    pthread_attr_t attr;
    pthread_attr_init(&attr);
	//pthread_attr_setdetachstate 修改线程的分离状态属性，可以使用pthread_attr_setdetachstate函数把线程属性detachstate设置为下面的两个合法值之一：设置为PTHREAD_CREATE_DETACHED,以分离状态启动线程；或者设置为PTHREAD_CREATE_JOINABLE,正常启动线程。线程的分离状态决定一个线程以什么样的方式来终止自己。在默认情况下线程是非分离状态的，这种情况下，原有的线程等待创建的线程结束。只有当pthread_join（）函数返回时，创建的线程才算终止，才能释放自己占用的系统资源。
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);
	//pthread_create的四个参数：1指向线程标识符的指针 2 设置线程属性 3 线程运行函数的起始地址 4 运行函数的参数。
	// pthread_create将会创建线程,在线程创建以后，就开始运行相关的线程函数
	// 因此在BlockImageUpdateFn中将会创建出一个线程,
    //线程标识符--new_data_thread,   //线程属性attr设置为了PTHREAD_CREATE_JOINABLE,代表非分离线程,非分离的线程终止时，其线程ID和退出状态将保留，直到另外一个线程调用pthread_join.
    // 线程函数的起始地址, 这里就是执行unzip_new_data函数
    //nti--传给unzip_new_data函数的参数 
    pthread_create(&new_data_thread, &attr, unzip_new_data, &nti);

    int i, j;

    char* linesave;
    char* wordsave;

    // 代开文件/dev/block/bootdevice/by-name/system
    int fd = open(blockdev_filename->data, O_RDWR);
    if (fd < 0) {
        ErrorAbort(state, "failed to open %s: %s", blockdev_filename->data, strerror(errno));
        goto done;
    }

    // line用于保存transfer.list文件的每一单行
    char* line;
    char* word;

    // The data in transfer_list_value is not necessarily
    // null-terminated, so we need to copy it to a new buffer and add
    // the null that strtok_r will need.
    // 分配一段内存,在之后用于保存transfer.list文件所有内容,transfer_list指向分配的这段内存
    transfer_list = malloc(transfer_list_value->size+1);
    if (transfer_list == NULL) {
        fprintf(stderr, "failed to allocate %zd bytes for transfer list\n",
                transfer_list_value->size+1);
        exit(1);
    }
	//将system.transfer.list文件的所有内容读取到了transfer_list指向的内存中
    memcpy(transfer_list, transfer_list_value->data, transfer_list_value->size);
	//按行分割读取system.transfer.list中的命令
    transfer_list[transfer_list_value->size] = '\0';

    line = strtok_r(transfer_list, "\n", &linesave);

    // first line in transfer list is the version number; currently
    // there's only version 1.
	// recovery 5.0 lollipop-erlease对应的api是1
	// d83e4f15890ac6ebe0d61924bd224eb1ae8565ad support for version 2 of block image diffs Change-Id: I4559bfd76d5403859637aeac832f3a5e9e13b63a 开始新增V2
	// 90221205a3e58f2a198faa838088dc7bc7c9c752 Support resuming block based OTAs Change-Id: I1e752464134aeb2d396946348e6041acabe13942 开始新增V3
    if (strcmp(line, "1") != 0) {
        ErrorAbort(state, "unexpected transfer list version [%s]\n", line);
        goto done;
    }

    // second line in transfer list is the total number of blocks we
    // expect to write.
    line = strtok_r(NULL, "\n", &linesave);
    int total_blocks = strtol(line, NULL, 0);
    // shouldn't happen, but avoid divide by zero.
    if (total_blocks == 0) ++total_blocks;
    int blocks_so_far = 0;

    uint8_t* buffer = NULL;
    size_t buffer_alloc = 0;

    // third and subsequent lines are all individual transfer commands.
	// 在这个for循环中依次读取每行命令
    for (line = strtok_r(NULL, "\n", &linesave); line;
         line = strtok_r(NULL, "\n", &linesave)) {
		// style代表每行前的命令名称，如move，bsdiff等	
        char* style;
        style = strtok_r(line, " ", &wordsave);

		// move b569d4f018e1cdda840f427eddc08a57b93d8c2e(sha1加密值,长度为40位) 2,545836,545840 4 2,545500,545504
        // sha256--64 sha512--128
        // move 2,545836,545840 2,545500,545504
		//处理system.transfer.list中的move命令
        if (strcmp("move", style) == 0) {
            word = strtok_r(NULL, " ", &wordsave);
			//将2,545836,545840 解析为src的range
            RangeSet* src = parse_range(word);
            word = strtok_r(NULL, " ", &wordsave);
			//将2,545500,545504 解析为tgt的range
            RangeSet* tgt = parse_range(word);

            printf("  moving %d blocks\n", src->size);

			//按src range大小申请buffer, 申请成功块个数记为buffer_alloc,正常情况下*buffer_alloc = size
            allocate(src->size * BLOCKSIZE, &buffer, &buffer_alloc);
            size_t p = 0;
            for (i = 0; i < src->count; ++i) {
                check_lseek(fd, (off64_t)src->pos[i*2] * BLOCKSIZE, SEEK_SET);
                size_t sz = (src->pos[i*2+1] - src->pos[i*2]) * BLOCKSIZE;
				//从blockdev_filename->data中取偏移,将读到的内容保存到上面申请的buffer
                readblock(fd, buffer+p, sz);
                p += sz;
            }

            p = 0;
            for (i = 0; i < tgt->count; ++i) {
                check_lseek(fd, (off64_t)tgt->pos[i*2] * BLOCKSIZE, SEEK_SET);
                size_t sz = (tgt->pos[i*2+1] - tgt->pos[i*2]) * BLOCKSIZE;
				//从blockdev_filename->data中取偏移,将buffer中的内容写入blockdev_filename->data
                writeblock(fd, buffer+p, sz);
                p += sz;
            }

			//blocks_so_far在 for (line = strtok_r(NULL, "\n", &linesave)开始前初始化为0
            blocks_so_far += tgt->size;
			//total_blocks是从transfer.list第二行读取的值,代表总共要写入的block数目
            fprintf(cmd_pipe, "set_progress %.4f\n", (double)blocks_so_far / total_blocks);
            fflush(cmd_pipe);

            free(src);
            free(tgt);

        } else if (strcmp("zero", style) == 0 ||
		//处理zero, 如果定义了DEBUG_ERASE为1, 这时erase mean fill the region with zeroes, 和zero的行为实际一样
		//zero //30,32770,32825,32827,33307,65535,65536,65538,66018,98303,98304,98306,98361,98363,98843,131071,131072,131074,131554,162907,163840,163842,16///3897,163899,164379,196607,196608,196610,197090,215039,215040
                   (DEBUG_ERASE && strcmp("erase", style) == 0)) {
		    //得到zero后的30及30个block编号,传给word
            word = strtok_r(NULL, " ", &wordsave);
			//将word所有信息解析,保存到tgt结构体中.
            RangeSet* tgt = parse_range(word);

			//tgt->size = 30个block组成的15个范围的 (右边-左边) 之和
            printf("  zeroing %d blocks\n", tgt->size);

			//调用allocate, 分配BLOCKSIZE大小的内存给buffer,buffer_alloc保存实际分配成功的内存大小
            allocate(BLOCKSIZE, &buffer, &buffer_alloc);
			//将buffer指向的BLOCKSIZE大小的这段内存全部写为0
            memset(buffer, 0, BLOCKSIZE);
			//调用check_lseek取得15个block区间每个范围的左边.
            for (i = 0; i < tgt->count; ++i) {
                check_lseek(fd, (off64_t)tgt->pos[i*2] * BLOCKSIZE, SEEK_SET);
				//调用writeblock,向每个block区间写入 这个区间长度 次,每次将大小为BLOCKSIZE的内存块buffer写入到fd
                for (j = tgt->pos[i*2]; j < tgt->pos[i*2+1]; ++j) {
					// 由于buffer指向的内存都是0, 因此实现了填0操作.
                    writeblock(fd, buffer, BLOCKSIZE);
                }
            }

            if (style[0] == 'z') {   // "zero" but not "erase"
                //对于zero命令还要把一共填0的block的数目累加, 计算 total_blocks已经处理 的百分比
                blocks_so_far += tgt->size;
                fprintf(cmd_pipe, "set_progress %.4f\n", (double)blocks_so_far / total_blocks);
                fflush(cmd_pipe);
            }

            free(tgt);
        } else if (strcmp("new", style) == 0) {
            //new //30,0,32770,32825,32827,33307,65535,65536,65538,66018,98303,98304,98306,98361,98363,98843,131071,131072,131074,131554,162907,163840,163842,163897,163899,164379,196607,//196608,196610,197090,215039
            //$ file system.new.dat
            // system.new.dat: Linux rev 1.0 ext2 filesystem data, UUID=da594c53-9beb-f85c-85c5-cedf76546f7a, volume name "system" (extents) (large files)

            // word 指向30后所有信息
            word = strtok_r(NULL, " ", &wordsave);
            // tgt保存30后所有信息
            RangeSet* tgt = parse_range(word);

            printf("  writing %d blocks of new data\n", tgt->size);

            RangeSinkState rss;
            rss.fd = fd;
            rss.tgt = tgt;
            rss.p_block = 0;
            rss.p_remain = (tgt->pos[1] - tgt->pos[0]) * BLOCKSIZE;
            check_lseek(fd, (off64_t)tgt->pos[0] * BLOCKSIZE, SEEK_SET);

            pthread_mutex_lock(&nti.mu);
            nti.rss = &rss;
            pthread_cond_broadcast(&nti.cv);
            while (nti.rss) {
                pthread_cond_wait(&nti.cv, &nti.mu);
            }
            pthread_mutex_unlock(&nti.mu);

            blocks_so_far += tgt->size;
            fprintf(cmd_pipe, "set_progress %.4f\n", (double)blocks_so_far / total_blocks);
            fflush(cmd_pipe);

            free(tgt);

        } else if (strcmp("bsdiff", style) == 0 ||
                   strcmp("imgdiff", style) == 0) {
            // bsdiff 0(patch_offset) 35581(patch_len) 67a63498a1293c14e23768bf7200348b8837e949 9c06e7e0277dee8c98e9a8b2a10d8649f6cfb3b0 2,367217,368194 979 2,367217,368196
// imgdiff 134034 2022 192e81959ac1985b1d90962faae1286029d4f39e 021c103903aa2da3ef222e1da5bdccdee287d1c3 2,40903,41035 132 2,40904,41036
// bsdiff 0(patch_offset) 35581(patch_len) 2,367217,368194(src_range) 2,367217,368196(tgt_range)
// imgdiff 134034(patch_offset) 2022(patch_len) 2,40903,41035(src_range) 132 2,40904,41036(tgt_range)
    //    bsdiff patchstart patchlen [src rangeset] [tgt rangeset]
    //    imgdiff patchstart patchlen [src rangeset] [tgt rangeset]
    //      - read the source blocks, apply a patch, write result to
    //        target blocks.  bsdiff or imgdiff specifies the type of
    //        patch.
            word = strtok_r(NULL, " ", &wordsave);
            size_t patch_offset = strtoul(word, NULL, 0);
            word = strtok_r(NULL, " ", &wordsave);
            size_t patch_len = strtoul(word, NULL, 0);

            word = strtok_r(NULL, " ", &wordsave);
            RangeSet* src = parse_range(word);
            word = strtok_r(NULL, " ", &wordsave);
            RangeSet* tgt = parse_range(word);

            printf("  patching %d blocks to %d\n", src->size, tgt->size);

            // Read the source into memory.
            //调用allocate, 分配BLOCKSIZE大小的内存给buffer,buffer_alloc保存实际分配成功的内存大小
            allocate(src->size * BLOCKSIZE, &buffer, &buffer_alloc);
            size_t p = 0;
            for (i = 0; i < src->count; ++i) {
                check_lseek(fd, (off64_t)src->pos[i*2] * BLOCKSIZE, SEEK_SET);
                size_t sz = (src->pos[i*2+1] - src->pos[i*2]) * BLOCKSIZE;
                //从blockdev_filename->data中取偏移,将读到的内容保存到上面申请的buffer
                readblock(fd, buffer+p, sz);
                p += sz;
            }

            Value patch_value;
            patch_value.type = VAL_BLOB;
            patch_value.size = patch_len;
            //patch_start 指向的地址就是 ota zip包中文件system.patch.dat的地址
            patch_value.data = (char*)(patch_start + patch_offset);

            RangeSinkState rss;
            rss.fd = fd;
            rss.tgt = tgt;
            rss.p_block = 0;
            rss.p_remain = (tgt->pos[1] - tgt->pos[0]) * BLOCKSIZE;
            check_lseek(fd, (off64_t)tgt->pos[0] * BLOCKSIZE, SEEK_SET);

            if (style[0] == 'i') {      // imgdiff
                ApplyImagePatch(buffer, src->size * BLOCKSIZE,
                                &patch_value,
                                &RangeSinkWrite, &rss, NULL, NULL);
            } else {
                ApplyBSDiffPatch(buffer, src->size * BLOCKSIZE,
                                 &patch_value, 0,
                                 &RangeSinkWrite, &rss, NULL);
            }

            // We expect the output of the patcher to fill the tgt ranges exactly.
            // 打完pathc后rss.p_block就是新生成的目标大小
            if (rss.p_block != tgt->count || rss.p_remain != 0) {
                //对于ApplyImagePatch或ApplyBSDiffPatch,都是在RangeSinkWrite中完成rss->p_remain-=write_now 正常情况下rss.p_remain应为0
                fprintf(stderr, "range sink underrun?\n");
            }

            blocks_so_far += tgt->size;
            fprintf(cmd_pipe, "set_progress %.4f\n", (double)blocks_so_far / total_blocks);
            fflush(cmd_pipe);

            free(src);
            free(tgt);
        } else if (!DEBUG_ERASE && strcmp("erase", style) == 0) {
            //DEBUG_ERASE 默认为0, 这时执行system.transfer.list中的erase命令时
            //erase 14,546363,556544,557570,589312,590338,622080,623106,654848,655874,687616,688642,720384,721410,753152
            struct stat st;
            //先根据open(blockdev_filename->data)读到的fd 判断target是不是块设备
            if (fstat(fd, &st) == 0 && S_ISBLK(st.st_mode)) {
                word = strtok_r(NULL, " ", &wordsave);
                // word 14,546363,....,753152
                RangeSet* tgt = parse_range(word);

                printf("  erasing %d blocks\n", tgt->size);

                for (i = 0; i < tgt->count; ++i) {
                    uint64_t range[2];
                    // offset in bytes
                    // range[0] 每个区间的起始位置
                    range[0] = tgt->pos[i*2] * (uint64_t)BLOCKSIZE;
                    // len in bytes
                    // range[1] 每个区间的长度
                    range[1] = (tgt->pos[i*2+1] - tgt->pos[i*2]) * (uint64_t)BLOCKSIZE;

                    // #define BLKDISCARD _IO(0x12,119)blkdiscard is used to discard device sectors.This is useful for solid-state drivers (SSDs) and thinly-provisioned storage 
                    //调用ioctl屏蔽range描述的块组区间
                    if (ioctl(fd, BLKDISCARD, &range) < 0) {
                        printf("    blkdiscard failed: %s\n", strerror(errno));
                    }
                }

                free(tgt);
            } else {
                printf("  ignoring erase (not block device)\n");
            }
        } else {
            fprintf(stderr, "unknown transfer style \"%s\"\n", style);
            exit(1);
        }
    }

    pthread_join(new_data_thread, NULL);
    success = true;

    free(buffer);
    printf("wrote %d blocks; expected %d\n", blocks_so_far, total_blocks);
    printf("max alloc needed was %zu\n", buffer_alloc);

  done:
    free(transfer_list);
    FreeValue(blockdev_filename);
    FreeValue(transfer_list_value);
    FreeValue(new_data_fn);
    FreeValue(patch_data_fn);
    return StringValue(success ? strdup("t") : strdup(""));
}

//if (range_sha1("/dev/block/platform/mtk-msdc.0/11230000.msdc0/by-name/syst
//em", "72,1,32770,32929,32931,33439,65535,65536,65538,66046,98303,98304,98306,98465,98467,98975,131071,131072,131074,131582,163839,163840,163842,164001,164003,164511,196607,196608,196610,197118,22
//9375,229376,229378,229537,229539,230047,262143,262144,262146,262654,294911,294912,294914,295073,295075,295583,327679,327680,327682,328190,355086,360448,360450,393216,393218,425984,425986,458752,458754,491520,491522,524288,524290,557056,557058,589824,589826,622592,622594,623102,650190,650191,655320") == "3168346b9a857c0dd0e962e86032bf464a007957" || block_image_verify("/dev/block/platform/mtk-msdc.0/11230000.msdc0/by-name/system", package_extract_file("system.transfer.list"), "system.new.dat", "system.patch.dat")) then
Value* RangeSha1Fn(const char* name, State* state, int argc, Expr* argv[]) {
    Value* blockdev_filename;
    Value* ranges;
    const uint8_t* digest = NULL;
    // 解析range_sha1的分区路径到blockdev_filename,解析区间范围参数到ranges
    if (ReadValueArgs(state, argv, 2, &blockdev_filename, &ranges) < 0) {
        return NULL;
    }

    if (blockdev_filename->type != VAL_STRING) {
        ErrorAbort(state, "blockdev_filename argument to %s must be string", name);
        goto done;
    }
    if (ranges->type != VAL_STRING) {
        ErrorAbort(state, "ranges argument to %s must be string", name);
        goto done;
    }

    // 打开/dev/block/platform/mtk-msdc.0/11230000.msdc0/by-name/system设备节点
    int fd = open(blockdev_filename->data, O_RDWR);
    if (fd < 0) {
        ErrorAbort(state, "failed to open %s: %s", blockdev_filename->data, strerror(errno));
        goto done;
    }

    // ranges->data指向"72,1,32770,32...",将这72个区间段解析后保存到rs
    RangeSet* rs = parse_range(ranges->data);
    // buffer大小刚好是1个block
    uint8_t buffer[BLOCKSIZE];

    SHA_CTX ctx;
    SHA_init(&ctx);

    int i, j;
    // 在for循环中累计更新这72个区间的hash,累计完后一次性计算sha1
    for (i = 0; i < rs->count; ++i) {
        check_lseek(fd, (off64_t)rs->pos[i*2] * BLOCKSIZE, SEEK_SET);
        // 这个for中更新每个区间内所有block的hash
        for (j = rs->pos[i*2]; j < rs->pos[i*2+1]; ++j) {
            //每循环一次读取1个block,并更新hash
            readblock(fd, buffer, BLOCKSIZE);
            SHA_update(&ctx, buffer, BLOCKSIZE);
        }
    }
    // digest就是最终这72个区间的sha1,range_sha1返回digest的值,在if中和3168346b9a857c0dd0e962e86032bf464a007957比较
    digest = SHA_final(&ctx);
    close(fd);

  done:
    FreeValue(blockdev_filename);
    FreeValue(ranges);
    if (digest == NULL) {
        // 如果digest为空,则range_sha1就返回""
        return StringValue(strdup(""));
    } else {
        // 正常情况
        return StringValue(PrintSha1(digest));
    }
}

void RegisterBlockImageFunctions() {
    RegisterFunction("block_image_update", BlockImageUpdateFn);
    RegisterFunction("range_sha1", RangeSha1Fn);
}
