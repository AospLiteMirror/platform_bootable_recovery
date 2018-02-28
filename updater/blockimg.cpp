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
#include <linux/fs.h>
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
#include <fec/io.h>

#include <map>
#include <memory>
#include <string>
#include <vector>

#include <android-base/parseint.h>
#include <android-base/strings.h>

#include "applypatch/applypatch.h"
#include "edify/expr.h"
#include "error_code.h"
#include "install.h"
#include "openssl/sha.h"
//Split individual transfer list commands into separate functions with unified parameters for clarity, and use a hash table to locate them during execution.
#include "minzip/Hash.h"
#include "ota_io.h"
#include "print_sha1.h"
#include "unique_fd.h"
#include "updater.h"

#define BLOCKSIZE 4096

// Set this to 0 to interpret 'erase' transfers to mean do a
// BLKDISCARD ioctl (the normal behavior).  Set to 1 to interpret
// erase to mean fill the region with zeroes.
#define DEBUG_ERASE  0

#define STASH_DIRECTORY_BASE "/cache/recovery"
#define STASH_DIRECTORY_MODE 0700
#define STASH_FILE_MODE 0600

struct RangeSet {
    size_t count;             // Limit is INT_MAX.
    size_t size;
    std::vector<size_t> pos;  // Actual limit is INT_MAX.
};

static CauseCode failure_type = kNoCause;
static bool is_retry = false;
static std::map<std::string, RangeSet> stash_map;

//在BlockImageUpdateFn中的调用情况为:  RangeSet* tgt = parse_range(word);
//这时word指向的是 30,32770,32825,32827,33307,65535,65536,65538,66018,98303,98304,98306,98361,98363,98843,131071,131072,131074,131554,162907,163840,163842,16///3897,163899,164379,196607,196608,196610,197090,215039,215040
static void parse_range(const std::string& range_text, RangeSet& rs) {
    std::vector<std::string> pieces = android::base::Split(range_text, ",");
    if (pieces.size() < 3) {
        goto err;
    }

    size_t num;
    //将text最前面的 block编号 个数30 给num
    if (!android::base::ParseUint(pieces[0].c_str(), &num, static_cast<size_t>(INT_MAX))) {
        goto err;
    }

    if (num == 0 || num % 2) {
        goto err; // must be even
    } else if (num != pieces.size() - 1) {
        goto err;
    }

    rs.pos.resize(num);
    // 30个block编号,num=30,  两个block编号构成一个区间, 一共15个范围
    rs.count = num / 2;
    rs.size = 0;

    for (size_t i = 0; i < num; i += 2) {
        //30个rs.pos[i] 就保存的是每个block编号
        if (!android::base::ParseUint(pieces[i+1].c_str(), &rs.pos[i],
                                      static_cast<size_t>(INT_MAX))) {
            goto err;
        }

        if (!android::base::ParseUint(pieces[i+2].c_str(), &rs.pos[i+1],
                                      static_cast<size_t>(INT_MAX))) {
            goto err;
        }

        if (rs.pos[i] >= rs.pos[i+1]) {
            goto err; // empty or negative range
        }

        size_t sz = rs.pos[i+1] - rs.pos[i];
        if (rs.size > SIZE_MAX - sz) {
            goto err; // overflow
        }

        rs.size += sz;
    }
    //for循环执行完, rs.size就= (32825 - 32770) + (33370 - 32827) + ..... 15个范围每个的右边减左边

    return;

err:
    fprintf(stderr, "failed to parse range '%s'\n", range_text.c_str());
    exit(1);
}

static bool range_overlaps(const RangeSet& r1, const RangeSet& r2) {
    for (size_t i = 0; i < r1.count; ++i) {
        size_t r1_0 = r1.pos[i * 2];
        size_t r1_1 = r1.pos[i * 2 + 1];

        for (size_t j = 0; j < r2.count; ++j) {
            size_t r2_0 = r2.pos[j * 2];
            size_t r2_1 = r2.pos[j * 2 + 1];

            if (!(r2_0 >= r1_1 || r1_0 >= r2_1)) {
                return true;
            }
        }
    }

    return false;
}

// 读取文件描述符fd指向数据到data,读取大小为size.成功返回0,失败返回-1
static int read_all(int fd, uint8_t* data, size_t size) {
    size_t so_far = 0;
    while (so_far < size) {
        ssize_t r = TEMP_FAILURE_RETRY(ota_read(fd, data+so_far, size-so_far));
        if (r == -1) {
            failure_type = kFreadFailure;
            fprintf(stderr, "read failed: %s\n", strerror(errno));
            return -1;
        }
        so_far += r;
    }
    return 0;
}

static int read_all(int fd, std::vector<uint8_t>& buffer, size_t size) {
    return read_all(fd, buffer.data(), size);
}

// 将data指向的大小为size的数据写入fd,成功返回0,失败返回-1
static int write_all(int fd, const uint8_t* data, size_t size) {
    size_t written = 0;
    while (written < size) {
        ssize_t w = TEMP_FAILURE_RETRY(ota_write(fd, data+written, size-written));
        if (w == -1) {
            failure_type = kFwriteFailure;
            fprintf(stderr, "write failed: %s\n", strerror(errno));
            return -1;
        }
        written += w;
    }

    return 0;
}

static int write_all(int fd, const std::vector<uint8_t>& buffer, size_t size) {
    return write_all(fd, buffer.data(), size);
}

static bool discard_blocks(int fd, off64_t offset, uint64_t size) {
    // Don't discard blocks unless the update is a retry run.
    if (!is_retry) {
        return true;
    }

    uint64_t args[2] = {static_cast<uint64_t>(offset), size};
    int status = ioctl(fd, BLKDISCARD, &args);
    if (status == -1) {
        fprintf(stderr, "BLKDISCARD ioctl failed: %s\n", strerror(errno));
        return false;
    }
    return true;
}

// check_lseek函数用于设置写入的偏移量,定位写入位置
// 成功返回0,失败返回-1
static bool check_lseek(int fd, off64_t offset, int whence) {
    off64_t rc = TEMP_FAILURE_RETRY(lseek64(fd, offset, whence));
    if (rc == -1) {
        failure_type = kLseekFailure;
        fprintf(stderr, "lseek64 failed: %s\n", strerror(errno));
        return false;
    }
    return true;
}

// 申请一段内存,buffer指向首地址
// buffer -- 申请到的内存的首地址
// buffer_alloc -- 已经申请到的内存的大小, 以1个BLOCKSIZE(4096字节)为单位
// size -- 要申请的内存的大小, 以1个BLOCKSIZE为单位
static void allocate(size_t size, std::vector<uint8_t>& buffer) {
    // if the buffer's big enough, reuse it.
    // 如果buffer_alloc >= size, 说明buffer指向的内存>=size,就没必须继续申请,可以重用buffer,
    if (size <= buffer.size()) return;

    buffer.resize(size);
}

struct RangeSinkState {
    RangeSinkState(RangeSet& rs) : tgt(rs) { };

    int fd;
    const RangeSet& tgt;
    size_t p_block;
    size_t p_remain;
};

// 在RangeSinkWrite中实现将system.new.data解压后的数据写入target的功能
// RangeSinkWrite 相对于函数FileSink和MemorySink,是将一个区间段数据写入闪存
// 1 在BlockImageUpdateFn中执行transfer.list中的imgdiff或bsdiff命令时,调用ApplyImagePatch或ApplyBSDiffPatch时传入的sink函数指针
// 2 receive_new_data中直接调用
// data -- 要写入的数据的起始地址
// size -- 要写入的数据大小
// token -- 
static ssize_t RangeSinkWrite(const uint8_t* data, ssize_t size, void* token) {
    RangeSinkState* rss = reinterpret_cast<RangeSinkState*>(token);

    // 对于BlockImageUpdateFn中的调用,	RangeSinkState rss; rss.p_remain = (tgt->pos[1] - tgt->pos[0]) * BLOCKSIZE;
    // RangeSinkState的p_remain代表剩余要从内存写入闪存的数据大小
    if (rss->p_remain == 0) {
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

        // 移动要写入的数据的地址
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
            // 如果p_block<总区段个数, 就继续更新下一个block区间
            if (rss->p_block < rss->tgt.count) {
                rss->p_remain = (rss->tgt.pos[rss->p_block * 2 + 1] -
                                 rss->tgt.pos[rss->p_block * 2]) * BLOCKSIZE;

                off64_t offset = static_cast<off64_t>(rss->tgt.pos[rss->p_block*2]) * BLOCKSIZE;
                if (!discard_blocks(rss->fd, offset, rss->p_remain)) {
                    break;
                }

                // 调用check_lseek,将读写位置指向下一个block区间起始位置
                if (!check_lseek(rss->fd, offset, SEEK_SET)) {
                    break;
                }

            } else {
                // we can't write any more; return how many bytes have
                // been written so far.
                // 说明已经更新完所有block区间, 返回已经写入的数据的大小
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

struct NewThreadInfo {
    ZipArchive* za;
    const ZipEntry* entry;

    RangeSinkState* rss;

    pthread_mutex_t mu;
    pthread_cond_t cv;
};

// 相关调用顺序为:BlockImageUpdateFn--unzip_new_data--mzProcessZipEntryContents--processDeflatedEntry或processStoredEntry--receive_new_data
static bool receive_new_data(const unsigned char* data, int size, void* cookie) {
    NewThreadInfo* nti = reinterpret_cast<NewThreadInfo*>(cookie);

    while (size > 0) {
        // Wait for nti->rss to be non-null, indicating some of this
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
        while (nti->rss == nullptr) {
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

        if (nti->rss->p_block == nti->rss->tgt.count) {
            // we have written all the bytes desired by this rss.

            pthread_mutex_lock(&nti->mu);
            //解压system.new.data的数据都写入完后将nti->rss=NULL
            nti->rss = nullptr;
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
    return nullptr;
}

// 传入的src为source block的范围,将src表示的范围内的数据读取到buffer中
static int ReadBlocks(const RangeSet& src, std::vector<uint8_t>& buffer, int fd) {
    size_t p = 0;
    uint8_t* data = buffer.data();

    // 在这个for中把src rangeset表示的所有block区间的数据读到buffer指向的内存中
    for (size_t i = 0; i < src.count; ++i) {
        if (!check_lseek(fd, (off64_t) src.pos[i * 2] * BLOCKSIZE, SEEK_SET)) {
            return -1;
        }

        size_t size = (src.pos[i * 2 + 1] - src.pos[i * 2]) * BLOCKSIZE;

        //从blockdev_filename->data中取偏移,将读到的内容保存到上面申请的buffer
        if (read_all(fd, data + p, size) == -1) {
            return -1;
        }

        p += size;
    }

    return 0;
}

// 传入的tgt为target block的范围, 将buffer内的数据写入到tgt表示的范围内的target block
static int WriteBlocks(const RangeSet& tgt, const std::vector<uint8_t>& buffer, int fd) {
    const uint8_t* data = buffer.data();

    size_t p = 0;
    for (size_t i = 0; i < tgt.count; ++i) {
        off64_t offset = static_cast<off64_t>(tgt.pos[i * 2]) * BLOCKSIZE;
        size_t size = (tgt.pos[i * 2 + 1] - tgt.pos[i * 2]) * BLOCKSIZE;
        if (!discard_blocks(fd, offset, size)) {
            return -1;
        }

        if (!check_lseek(fd, offset, SEEK_SET)) {
            return -1;
        }

        if (write_all(fd, data + p, size) == -1) {
            return -1;
        }

        p += size;
    }

    return 0;
}

// Parameters for transfer list command functions
struct CommandParameters {
    std::vector<std::string> tokens;
    size_t cpos;
    const char* cmdname;
    const char* cmdline;
    std::string freestash;
    std::string stashbase;
    bool canwrite;
    int createdstash;
    int fd;
    bool foundwrites;
    bool isunresumable;
    int version;
    size_t written;
    size_t stashed;
    NewThreadInfo nti;
    pthread_t thread;
    std::vector<uint8_t> buffer;
    uint8_t* patch_start;
};

// Do a source/target load for move/bsdiff/imgdiff in version 1.
// We expect to parse the remainder of the parameter tokens as:
//
//    <src_range> <tgt_range>
//
// The source range is loaded into the provided buffer, reallocating
// it to make it larger if necessary.

// V2中stash命令调用为LoadSrcTgtVersion1(wordsave, NULL, &src_blocks,	stash_table + stash_id, &stash_alloc, fd);
// 对于stash命令,1 解析按src RangeSet命令后面就没有tgt RangeSet,因此调用时tgt必须传NULL
// 2 V1的move等将src RangeSet范围的block加载到申请的buffer中,
// 而V2的stash等将src RangeSet范围的block加载到之前申请的stash table指向的内存中
static int LoadSrcTgtVersion1(CommandParameters& params, RangeSet& tgt, size_t& src_blocks,
        std::vector<uint8_t>& buffer, int fd) {

    if (params.cpos + 1 >= params.tokens.size()) {
        fprintf(stderr, "invalid parameters\n");
        return -1;
    }

    // <src_range>
    RangeSet src;
    //将2,545836,545840 解析为src的range
    parse_range(params.tokens[params.cpos++], src);

    // <tgt_range>
    //将2,545500,545504 解析为tgt的range
    parse_range(params.tokens[params.cpos++], tgt);

    // 按src range的block个数(src->size)申请内存, buffer指向申请到的内存首地址,申请成功块个数传给buffer_alloc,正常情况下*buffer_alloc = size
    // 在allocate中会比较size和buffer_alloc,根据buffer_alloc含义,如果>size,就可以重用buffer,allocate可以直接返回
    // buffer_alloc保存实际分配成功的内存大小
    // 对于stash命令在保存 加载stash 的buffer,也是在这里完成分配
    allocate(src.size * BLOCKSIZE, buffer);
    int rc = ReadBlocks(src, buffer, fd);
    src_blocks = src.size;

    return rc;
}

// VerifyBlocks用于验证buffer中长度为blocks大小的数据的sha1,是否与期待值expected相同
// expected为调用VerifyBlocks时传入的sha1值
static int VerifyBlocks(const std::string& expected, const std::vector<uint8_t>& buffer,
        const size_t blocks, bool printerror) {
    uint8_t digest[SHA_DIGEST_LENGTH];
    const uint8_t* data = buffer.data();

    SHA1(data, blocks * BLOCKSIZE, digest);

    std::string hexdigest = print_sha1(digest);

    if (hexdigest != expected) {
        if (printerror) {
            fprintf(stderr, "failed to verify blocks (expected %s, read %s)\n",
                    expected.c_str(), hexdigest.c_str());
        }
        return -1;
    }

    return 0;
}

static std::string GetStashFileName(const std::string& base, const std::string& id,
        const std::string& postfix) {
    if (base.empty()) {
        return "";
    }

    std::string fn(STASH_DIRECTORY_BASE);
    //!!执行后fn指向字符串 "/cache/recovery/{哈希值}"
    fn += "/" + base + "/" + id + postfix;

    return fn;
}

typedef void (*StashCallback)(const std::string&, void*);

// Does a best effort enumeration of stash files. Ignores possible non-file
// items in the stash directory and continues despite of errors. Calls the
// 'callback' function for each file and passes 'data' to the function as a
// parameter.

// enumeration 列举 枚举
// EnumerateStash(dirname, DeletePartial, NULL);
// EnumerateStash(dirname, UpdateFileSize, &size);
// dirname -- /cache/recovery/{base}
// callback -- 函数DeletePartial或者UpdateFileSize
static void EnumerateStash(const std::string& dirname, StashCallback callback, void* data) {
    if (dirname.empty() || callback == nullptr) {
        return;
    }

    //调用opendir, 因为dirname指向的是一个文件夹
    std::unique_ptr<DIR, int(*)(DIR*)> directory(opendir(dirname.c_str()), closedir);

    if (directory == nullptr) {
        if (errno != ENOENT) {
            fprintf(stderr, "opendir \"%s\" failed: %s\n", dirname.c_str(), strerror(errno));
        }
        return;
    }

    struct dirent* item;
    //循环处理dirname文件夹下的所有文件和文件夹
    while ((item = readdir(directory.get())) != nullptr) {
        //对于不是常规文件的所有情况都直接跳过 DT_REG        This is a regular file.
        if (item->d_type != DT_REG) {
            continue;
        }

        //fn指向字符串 "/cache/recovery/{base}/{常规文件的文件名}"
        std::string fn = dirname + "/" + std::string(item->d_name);
        //在PerformBlockImageUpdate中先调用DeletePartial,再调用UpdateFileSize
        callback(fn, data);
    }
}

static void UpdateFileSize(const std::string& fn, void* data) {
    if (fn.empty() || !data) {
        return;
    }

    struct stat sb;
    if (stat(fn.c_str(), &sb) == -1) {
        fprintf(stderr, "stat \"%s\" failed: %s\n", fn.c_str(), strerror(errno));
        return;
    }

    int* size = reinterpret_cast<int*>(data);
    *size += sb.st_size;
}

// Deletes the stash directory and all files in it. Assumes that it only
// contains files. There is nothing we can do about unlikely, but possible
// errors, so they are merely logged.

static void DeleteFile(const std::string& fn, void* /* data */) {
    if (!fn.empty()) {
        fprintf(stderr, "deleting %s\n", fn.c_str());

        if (unlink(fn.c_str()) == -1 && errno != ENOENT) {
            fprintf(stderr, "unlink \"%s\" failed: %s\n", fn.c_str(), strerror(errno));
        }
    }
}

static void DeletePartial(const std::string& fn, void* data) {
    //如果/cache/recovery/{base}/下的文件 的文件名中有".partial",就删除这个文件
    if (android::base::EndsWith(fn, ".partial")) {
        DeleteFile(fn, data);
    }
}

static void DeleteStash(const std::string& base) {
    if (base.empty()) {
        return;
    }

    fprintf(stderr, "deleting stash %s\n", base.c_str());

    std::string dirname = GetStashFileName(base, "", "");
    EnumerateStash(dirname, DeleteFile, nullptr);

    if (rmdir(dirname.c_str()) == -1) {
        if (errno != ENOENT && errno != ENOTDIR) {
            fprintf(stderr, "rmdir \"%s\" failed: %s\n", dirname.c_str(), strerror(errno));
        }
    }
}

static int LoadStash(CommandParameters& params, const std::string& base, const std::string& id,
        bool verify, size_t* blocks, std::vector<uint8_t>& buffer, bool printnoent) {
    // In verify mode, if source range_set was saved for the given hash,
    // check contents in the source blocks first. If the check fails,
    // search for the stashed files on /cache as usual.
    if (!params.canwrite) {
        if (stash_map.find(id) != stash_map.end()) {
            const RangeSet& src = stash_map[id];
            allocate(src.size * BLOCKSIZE, buffer);

            if (ReadBlocks(src, buffer, params.fd) == -1) {
                fprintf(stderr, "failed to read source blocks in stash map.\n");
                return -1;
            }
            if (VerifyBlocks(id, buffer, src.size, true) != 0) {
                fprintf(stderr, "failed to verify loaded source blocks in stash map.\n");
                return -1;
            }
            return 0;
        }
    }

    if (base.empty()) {
        return -1;
    }

    size_t blockcount = 0;

    if (!blocks) {
        blocks = &blockcount;
    }

    std::string fn = GetStashFileName(base, id, "");

    struct stat sb;
    int res = stat(fn.c_str(), &sb);

    if (res == -1) {
        if (errno != ENOENT || printnoent) {
            fprintf(stderr, "stat \"%s\" failed: %s\n", fn.c_str(), strerror(errno));
        }
        return -1;
    }

    fprintf(stderr, " loading %s\n", fn.c_str());

    if ((sb.st_size % BLOCKSIZE) != 0) {
        fprintf(stderr, "%s size %" PRId64 " not multiple of block size %d",
                fn.c_str(), static_cast<int64_t>(sb.st_size), BLOCKSIZE);
        return -1;
    }

    int fd = TEMP_FAILURE_RETRY(open(fn.c_str(), O_RDONLY));
    unique_fd fd_holder(fd);

    if (fd == -1) {
        fprintf(stderr, "open \"%s\" failed: %s\n", fn.c_str(), strerror(errno));
        return -1;
    }

    allocate(sb.st_size, buffer);

    if (read_all(fd, buffer, sb.st_size) == -1) {
        return -1;
    }

    *blocks = sb.st_size / BLOCKSIZE;

    if (verify && VerifyBlocks(id, buffer, *blocks, true) != 0) {
        fprintf(stderr, "unexpected contents in %s\n", fn.c_str());
        DeleteFile(fn, nullptr);
        return -1;
    }

    return 0;
}

static int WriteStash(const std::string& base, const std::string& id, int blocks,
        std::vector<uint8_t>& buffer, bool checkspace, bool *exists) {
    if (base.empty()) {
        return -1;
    }

    if (checkspace && CacheSizeCheck(blocks * BLOCKSIZE) != 0) {
        fprintf(stderr, "not enough space to write stash\n");
        return -1;
    }

    std::string fn = GetStashFileName(base, id, ".partial");
    std::string cn = GetStashFileName(base, id, "");

    if (exists) {
        struct stat sb;
        int res = stat(cn.c_str(), &sb);

        if (res == 0) {
            // The file already exists and since the name is the hash of the contents,
            // it's safe to assume the contents are identical (accidental hash collisions
            // are unlikely)
            fprintf(stderr, " skipping %d existing blocks in %s\n", blocks, cn.c_str());
            *exists = true;
            return 0;
        }

        *exists = false;
    }

    fprintf(stderr, " writing %d blocks to %s\n", blocks, cn.c_str());

    int fd = TEMP_FAILURE_RETRY(open(fn.c_str(), O_WRONLY | O_CREAT | O_TRUNC, STASH_FILE_MODE));
    unique_fd fd_holder(fd);

    if (fd == -1) {
        fprintf(stderr, "failed to create \"%s\": %s\n", fn.c_str(), strerror(errno));
        return -1;
    }

    if (write_all(fd, buffer, blocks * BLOCKSIZE) == -1) {
        return -1;
    }

    if (ota_fsync(fd) == -1) {
        failure_type = kFsyncFailure;
        fprintf(stderr, "fsync \"%s\" failed: %s\n", fn.c_str(), strerror(errno));
        return -1;
    }

    if (rename(fn.c_str(), cn.c_str()) == -1) {
        fprintf(stderr, "rename(\"%s\", \"%s\") failed: %s\n", fn.c_str(), cn.c_str(),
                strerror(errno));
        return -1;
    }

    std::string dname = GetStashFileName(base, "", "");
    int dfd = TEMP_FAILURE_RETRY(open(dname.c_str(), O_RDONLY | O_DIRECTORY));
    unique_fd dfd_holder(dfd);

    if (dfd == -1) {
        failure_type = kFileOpenFailure;
        fprintf(stderr, "failed to open \"%s\" failed: %s\n", dname.c_str(), strerror(errno));
        return -1;
    }

    if (ota_fsync(dfd) == -1) {
        failure_type = kFsyncFailure;
        fprintf(stderr, "fsync \"%s\" failed: %s\n", dname.c_str(), strerror(errno));
        return -1;
    }

    return 0;
}

// Creates a directory for storing stash files and checks if the /cache partition
// hash enough space for the expected amount of blocks we need to store. Returns
// >0 if we created the directory, zero if it existed already, and <0 of failure.

// maxblocks -- system.transfer.list文件的第四行
// blockdev -- "/dev/block/bootdevice/by-name/system" 等分区的设备节点路径
// base -- blockdev 指向的字符串值 sha加密后的 字符串值
static int CreateStash(State* state, int maxblocks, const char* blockdev, std::string& base) {
    if (blockdev == nullptr) {
        return -1;
    }

    // Stash directory should be different for each partition to avoid conflicts
    // when updating multiple partitions at the same time, so we use the hash of
    // the block device name as the base directory
    uint8_t digest[SHA_DIGEST_LENGTH];
    SHA1(reinterpret_cast<const uint8_t*>(blockdev), strlen(blockdev), digest);
    // *base指向的就是/dev/block/bootdevice/by-name/system 的40位sha加密 字符串
    // /dev/block/bootdevice/by-name/system -- 2bdde8504898ccfcd2c59f20bb8c9c25f73bb524
    // "/dev/block/bootdevice/by-name/system" -- b00e5a7238619b2074783d82ba78f2c93f2653f9
    base = print_sha1(digest);

    // dirname 指向字符串 "/cache/recovery/{base}"
    std::string dirname = GetStashFileName(base, "", "");
    struct stat sb;
    //stat成功返回0,失败返回-1
    int res = stat(dirname.c_str(), &sb);

    // if else的两个分支都处理的是stat失败的情况
    if (res == -1 && errno != ENOENT) {
        // 获取/cache/recovery/{base}属性失败, 但失败原因不是因为/cache/recovery/{base}不存在(ENOENT)
        ErrorAbort(state, kStashCreationFailure, "stat \"%s\" failed: %s\n",
                   dirname.c_str(), strerror(errno));
        return -1;
    } else if (res != 0) {
        // 说明stat还是不成功,但失败原因就是/cache/recovery/{base}/文件夹不存在,这种情况下可以自行创建/cache/recovery/{base}
        fprintf(stderr, "creating stash %s\n", dirname.c_str());
        // mkdir!!! 创建出的/cache/recovery/{base}/是个文件夹,STASH_DIRECTORY_MODE 0700
        res = mkdir(dirname.c_str(), STASH_DIRECTORY_MODE);

        if (res != 0) {
            ErrorAbort(state, kStashCreationFailure, "mkdir \"%s\" failed: %s\n",
                       dirname.c_str(), strerror(errno));
            return -1;
        }

        // 在cahce分区分配 maxblocks * BLOCKSIZE 字节大小的空间
        if (CacheSizeCheck(maxblocks * BLOCKSIZE) != 0) {
            ErrorAbort(state, kStashCreationFailure, "not enough space for stash\n");
            return -1;
        }

        return 1;  // Created directory
    }

    fprintf(stderr, "using existing stash %s\n", dirname.c_str());

    // If the directory already exists, calculate the space already allocated to
    // stash files and check if there's enough for all required blocks. Delete any
    // partially completed stash files first.
    // 如果dirname(/cache/recovery/{base})文件夹已经存在的情况
    // 在DeletePartial中删除/cache/recovery/{base}/下所有文件名中含".partial"的普通文件
    EnumerateStash(dirname, DeletePartial, nullptr);
    int size = 0;
    //在UpdateFileSize中计算/cache/recovery/{base}/下所有剩余文件的大小总和(以字节为单位),传给size
    EnumerateStash(dirname, UpdateFileSize, &size);

    // 计算出cache分区还需要分配的空间大小
    size = maxblocks * BLOCKSIZE - size;

    // 如果cache分区分配 还需要分配的空间大小 失败
    if (size > 0 && CacheSizeCheck(size) != 0) {
        ErrorAbort(state, kStashCreationFailure, "not enough space for stash (%d more needed)\n",
                   size);
        return -1;
    }

    return 0; // Using existing directory
}

// SaveStash成功返回0,失败返回-1
static int SaveStash(CommandParameters& params, const std::string& base,
        std::vector<uint8_t>& buffer, int fd, bool usehash) {

    // <stash_id> <src_range>
    if (params.cpos + 1 >= params.tokens.size()) {
        fprintf(stderr, "missing id and/or src range fields in stash command\n");
        return -1;
    }
    // 对于v3,这里id就指向字符串"e271f3b2e779da7fb8374624b87bb0137b8a697a"
    const std::string& id = params.tokens[params.cpos++];

    size_t blocks = 0;
    //对于v3及以上,因为transfer.list命令参数中增加了可以用来验证的hash值,就调用LoadStash在读取要stash区块时再用hash做验证. hash就保存在id中
    if (usehash && LoadStash(params, base, id, true, &blocks, buffer, false) == 0) {
        // Stash file already exists and has expected contents. Do not
        // read from source again, as the source may have been already
        // overwritten during a previous attempt.
        return 0;
    }

    RangeSet src;
    parse_range(params.tokens[params.cpos++], src);

    allocate(src.size * BLOCKSIZE, buffer);
    if (ReadBlocks(src, buffer, fd) == -1) {
        return -1;
    }
    blocks = src.size;

    // 对于v3,在从src直接加载完后还可以利用id(hash值)再验证一次
    // 如果验证失败,说明src已经被修改. 但需要用到这块src的命令可能修改之前已经执行完了,所以忽略这种错误
    if (usehash && VerifyBlocks(id, buffer, blocks, true) != 0) {
        // Source blocks have unexpected contents. If we actually need this
        // data later, this is an unrecoverable error. However, the command
        // that uses the data may have already completed previously, so the
        // possible failure will occur during source block verification.
        fprintf(stderr, "failed to load source blocks for stash %s\n", id.c_str());
        return 0;
    }

    // In verify mode, save source range_set instead of stashing blocks.
    if (!params.canwrite && usehash) {
        stash_map[id] = src;
        return 0;
    }

    fprintf(stderr, "stashing %zu blocks to %s\n", blocks, id.c_str());
    params.stashed += blocks;
    // 最后将buffer中保存的要stash的数据写入到
    return WriteStash(base, id, blocks, buffer, false, nullptr);
}

// FreeStash中将会直接删除/cache/recovery/{hash值} 下暂存的文件
static int FreeStash(const std::string& base, const std::string& id) {
    if (base.empty() || id.empty()) {
        return -1;
    }

    std::string fn = GetStashFileName(base, id, "");
    DeleteFile(fn, nullptr);

    return 0;
}

// packed 异常拥挤的
// source含有部分可能会被overwrite的数据,
static void MoveRange(std::vector<uint8_t>& dest, const RangeSet& locs,
        const std::vector<uint8_t>& source) {
    // source contains packed data, which we want to move to the
    // locations given in locs in the dest buffer.  source and dest
    // may be the same buffer.

    const uint8_t* from = source.data();
    uint8_t* to = dest.data();
    size_t start = locs.size;
    for (int i = locs.count-1; i >= 0; --i) {
        size_t blocks = locs.pos[i*2+1] - locs.pos[i*2];
        start -= blocks;
        // memmove用于从src拷贝count个字节到dest，如果目标区域和源区域有重叠的话，memmove能够保证源串在被覆盖之前将
        // 但是当目标区域与源区域没有重叠则和memcpy函数功能相同
        // memcpy和memmove（）都是C语言中的库函数，在头文件string.h中，作用是拷贝一定长度的内存的内容
        // 他们的作用是一样的，唯一的区别是，当内存发生局部重叠的时候，memmove保证拷贝的结果是正确的，memcpy不保证他们的作用是一样的，唯一的区别是，当内存发生局部重叠的时候，memmove保证拷贝的结果是正确的，memcpy不保证
        memmove(to + (locs.pos[i*2] * BLOCKSIZE), from + (start * BLOCKSIZE),
                blocks * BLOCKSIZE);
    }
}

// Do a source/target load for move/bsdiff/imgdiff in version 2.
// We expect to parse the remainder of the parameter tokens as one of:
//
//    <tgt_range> <src_block_count> <src_range>
//        (loads data from source image only)
//
//    <tgt_range> <src_block_count> - <[stash_id:stash_range] ...>
//        (loads data from stashes only)
//
//    <tgt_range> <src_block_count> <src_range> <src_loc> <[stash_id:stash_range] ...>
//        (loads data from both source image and stashes)
//
// On return, buffer is filled with the loaded source data (rearranged
// and combined with stashed data as necessary).  buffer may be
// reallocated if needed to accommodate the source data.  *tgt is the
// target RangeSet.  Any stashes required are loaded using LoadStash.
// 任何需要的stash都是调用LoadStash加载的

static int LoadSrcTgtVersion2(CommandParameters& params, RangeSet& tgt, size_t& src_blocks,
        std::vector<uint8_t>& buffer, int fd, const std::string& stashbase, bool* overlap) {

    // At least it needs to provide three parameters: <tgt_range>,
    // <src_block_count> and "-"/<src_range>.
    if (params.cpos + 2 >= params.tokens.size()) {
        fprintf(stderr, "invalid parameters\n");
        return -1;
    }

    // <tgt_range>
    // 解析tgt的range
    //在PerformCommandMove和PerformCommandDiff中调用LoadSrcTgtVersion2之前有RangeSet* tgt = NULL;但这里传入的是tgt的地址,所以tgt肯定 != NULL
    parse_range(params.tokens[params.cpos++], tgt);

    // <src_block_count>
     //继续根据空格分割,读取src_block_count
    const std::string& token = params.tokens[params.cpos++];
    // 解析src_block_count,传给src_blocks
    if (!android::base::ParseUint(token.c_str(), &src_blocks)) {
        fprintf(stderr, "invalid src_block_count \"%s\"\n", token.c_str());
        return -1;
    }

    // 先从内存中申请buffer
    //根据src_blocks的大小分配一段buffer
    allocate(src_blocks * BLOCKSIZE, buffer);

    // "-" or <src_range> [<src_loc>]
    // 对应于move 2,449484,449485 1 - abe57036c22b8c5e4b3bee50ccad5a48ea72c4e3:2,0,1 这种情况,word这时就是"-" 走if的true分支,只从/cache分区的stash文件加载数据
    // <tgt_range> <src_block_count> - <[stash_id:stash_range] ...>
    if (params.tokens[params.cpos] == "-") {
        // no source ranges, only stashes
        params.cpos++;
    } else {
        // word这时就是"6,441913,442079,442080,442248,442249,442937"(src_range), 从source image和stash中都加载数据
        // 如果src_block_count后没有'-', 那么其后面至少有<src_range>,要么是<src_range>,要么是<src_range> <src_loc> <[stash_id:stash_range] ...>
        // 因此先解析src_range
        //对应于move 2,442249,443273 1024 6,441913,442079,442080,442248,442249,442937 6,0,166,167,335,336,1024 cd4bfd42982ed1a0ebd1efa9e029c618eb681f71:4,166,167,335,336这种情况,
        //<tgt_range> <src_block_count> <src_range> <src_loc> <[stash_id:stash_range] ...>
        //word这时就是src_range, "6,441913,442079,442080,442248,442249,442937"
        RangeSet src;
        parse_range(params.tokens[params.cpos++], src);
        int res = ReadBlocks(src, buffer, fd);

        if (overlap) {
            *overlap = range_overlaps(src, tgt);
        }

        if (res == -1) {
            return -1;
        }

        if (params.cpos >= params.tokens.size()) {
            // no stashes, only source range
            return 0;
        }

        RangeSet locs;
        // 继续解析<src_loc>
        parse_range(params.tokens[params.cpos++], locs);
        // 因为上面buffer中加载加载的全是source range,       调用MoveRange将source部分重叠区域的数据也移到buffer中对应同样位置中
        //调整buffer中src_range这段内容的位置为src_loc
        MoveRange(buffer, locs, buffer);
    }

    // <[stash_id:stash_range]>
    // 在while循环中解析<src_loc>后面的 <[stash_id:stash_range] ...>
    // 对于move 2,449484,449485 1 - abe57036c22b8c5e4b3bee50ccad5a48ea72c4e3:2,0,1 格式为(<tgt_range> <src_block_count> - <[stash_id:stash_range] ...>)
    // 多个[stash_id:stash_range]之间以空格分割,因此这个while循环就是解析最后剩余的所有[stash_id:stash_range],这里的例子只有一个
    while (params.cpos < params.tokens.size()) {
        // Each word is a an index into the stash table, a colon, and
        // then a rangeset describing where in the source block that
        // stashed data should go.
        //word指向"abe57036c22b8c5e4b3bee50ccad5a48ea72c4e3:2,0,1",执行后colon指向"abe57036c22b8c5e4b3bee50ccad5a48ea72c4e3" (stash_id)
        std::vector<std::string> tokens = android::base::Split(params.tokens[params.cpos++], ":");
        if (tokens.size() != 2) {
            fprintf(stderr, "invalid parameter\n");
            return -1;
        }

        std::vector<uint8_t> stash;
        // 这一步先读取/cache/recovery/{stashbase}/{colon}文件内容到&stash指向的内存空间中
        int res = LoadStash(params, stashbase, tokens[0], false, nullptr, stash, true);

        if (res == -1) {
            // These source blocks will fail verification if used later, but we
            // will let the caller decide if this is a fatal failure
            fprintf(stderr, "failed to load stash %s\n", tokens[0].c_str());
            continue;
        }

        RangeSet locs;
        // 解析出来的位置locs,stashed data最近一次执行stash命令从source lock加载时在source中的位置
        parse_range(tokens[1], locs);

        // 将这个stash_id指向的stashed的数据加载到buffer中locs位置
        MoveRange(buffer, locs, stash);
    }

    return 0;
}

// Do a source/target load for move/bsdiff/imgdiff in version 3.
//
// Parameters are the same as for LoadSrcTgtVersion2, except for 'onehash', which
// tells the function whether to expect separate source and targe block hashes, or
// if they are both the same and only one hash should be expected, and
// 'isunresumable', which receives a non-zero value if block verification fails in
// a way that the update cannot be resumed anymore.
// 参数与V2相同,除了"onehash",其用来 1 区别命令是否期待分隔的source和target block的hash,
// 如果source和target block相同则"onehash"只有一个hash值,否则"onehash"有两个hash值.
// 2 区别命令是否是"unresumable"(无法继续), 如果block验证失败会设置unresumable为一个非0值,
// unresumable设置为非0代表在某种程度上更新就不能继续进行

//
// If the function is unable to load the necessary blocks or their contents don't
// match the hashes, the return value is -1 and the command should be aborted.
//
// If the return value is 1, the command has already been completed according to
// the contents of the target blocks, and should not be performed again.
//
// If the return value is 0, source blocks have expected content and the command
// can be performed.

		
// PerformCommandMove和PerformCommandDiff中调用LoadSrcTgtVersion3时overlap都为0.
static int LoadSrcTgtVersion3(CommandParameters& params, RangeSet& tgt, size_t& src_blocks,
        bool onehash, bool& overlap) {

    if (params.cpos >= params.tokens.size()) {
        fprintf(stderr, "missing source hash\n");
        return -1;
    }

    // 对于bsdiff/imgdiff, params->cpos指向的就是bsdiff/imgdiff <patchstart> <patchlen> <...>的<...>
    // 对于move,params->cpos指向的就是move <...>的<...>
    std::string srchash = params.tokens[params.cpos++];
    std::string tgthash;

    // 对于bsdiff/imgdiff,调用LoadSrcTgtVersion3时onehash为0
    // 对于move,调用LoadSrcTgtVersion3时onehash为1
    if (onehash) {
        //如果onehash为0,说明tgt与src block数据相同
        tgthash = srchash;
    } else {
        // 如果onehash不为0,说明另存在tgthash
        if (params.cpos >= params.tokens.size()) {
            fprintf(stderr, "missing target hash\n");
            return -1;
        }
        tgthash = params.tokens[params.cpos++];
    }

    // 因为所有hash解析完后,命令中剩下的参数对于V3和V2都是完全一样的格式了,因此下来可以调用LoadSrcTgtVersion2来完成加载
    if (LoadSrcTgtVersion2(params, tgt, src_blocks, params.buffer, params.fd, params.stashbase,
            &overlap) == -1) {
        return -1;
    }

    // 在LoadSrcTgtVersion2中解析target rangeset,将相关信息保存到tgt中,这里根据tgt的大小分配buffer
    std::vector<uint8_t> tgtbuffer(tgt.size * BLOCKSIZE);

    // 根据tgt中包含的位置信息,从脚本中block_image_verify的第一个参数(/dev/block/bootdevice/by-name/system)读取对应位置数据到buffer中
    // 加载tgt block数据到tgtbuffer
    if (ReadBlocks(tgt, tgtbuffer, params.fd) == -1) {
        return -1;
    }

    // 验证tgt block数据的sha1是否等于tgthash
    if (VerifyBlocks(tgthash, tgtbuffer, tgt.size, false) == 0) {
        // Target blocks already have expected content, command should be skipped
    	// 如果tgt block数据的sha1等于tgthash,说明调用LoadSrcTgtVersion3的命令之前成功过
		// 因此可以直接设置返回值为1并跳过最后.这种情况很可能是升级过程中重启后才能遇到
		// 返回1代表按照tgt block的内容命令已经执行过了,而且不应该再次执行
        return 1;
    }

    // 如果tgt block数据的sha1不等于tgthash,再验证src block数据的sha1是否等于srchash
    // 能执行到这里要么是没有重启第一次刚执行调用V3的命令,要么是升级过程中强制重启,重启前tgt写到一半,重启后检测到tgt与tgthash不匹配
    // 在调用LoadSrcTgtVersion2时已经从source或(和)stash中读取数据到了params->buffer中,这里就可以验证与src hash是否匹配
    if (VerifyBlocks(srchash, params.buffer, src_blocks, true) == 0) {
   	    // 执行到这里说明从block_image_verify第一个参数读取到的target与tgt hash不匹配, 但
        // 从source或(和)stash中读取的数据(params->buffer)与src hash匹配, 这时再看source blocks和target blocks是否有重叠,
        // 如果有重叠,根据逻辑,因为要读的所有数据已经保存在了params->buffer中,所以还要调用WriteStash把params->buffer(其中保存了这段src blocks)全部再写入到/cache/recovery/{stashbase}/{srchash}这个文件中去. 
        // 写入的大小就是LoadSrcTgtVersion2中计算得到的src_blocks
        // If source and target blocks overlap, stash the source blocks so we can
        // resume from possible write errors. In verify mode, we can skip stashing
        // because the source blocks won't be overwritten.
        if (overlap && params.canwrite) {
            // 如果source blocks和target blocks有重叠,
            fprintf(stderr, "stashing %zu overlapping blocks to %s\n", src_blocks,
                    srchash.c_str());

            bool stash_exists = false;
            if (WriteStash(params.stashbase, srchash, src_blocks, params.buffer, true,
                           &stash_exists) != 0) {
                fprintf(stderr, "failed to stash overlapping source blocks\n");
                return -1;
            }

            params.stashed += src_blocks;
            // Can be deleted when the write has completed
            if (!stash_exists) {
                // 在WriteStash写入成功后可以将srchash保存到params->freestash中
                params.freestash = srchash;
            }
        }

        // 不管有没有重叠,这种情况都说明Source blocks have expected content, 到这里就可以跳到函数最后并返回0
        // 函数返回0代表source blocks与期待的匹配,命令可以执行
        // 正常升级没有任何中断重启的情况下,第一次执行的命令都是走到这里
        // Source blocks have expected content, command can proceed
        return 0;
    }

    // 执行到这里说明从block_image_verify第一个参数读取到的target与tgt hash不匹配, 同时从source或(和)stash中读取的数据(params->buffer)与src hash也不匹配
    // 这种情况下, 如果source blocks和target blocks有重叠,重叠的source blocks在之前会被暂存, 这时就可以调用LoadStash把之前暂停的stash文件(/cache/recovery/{stashbase}/{srchash})读取到params->buffer中.
    // 如果执行transfer.list中的命令时突然手机重启,重启后恢复更新就会走到这一步, 这种情况下无法判断stash是否可以删除
    if (overlap && LoadStash(params, params.stashbase, srchash, true, nullptr, params.buffer,
                             true) == 0) {
        // 如果LoadStash读取成功,到这里就可以跳到函数最后并返回0
        // Overlapping source blocks were previously stashed, command can proceed.
        // We are recovering from an interrupted command, so we don't know if the
        // stash can safely be deleted after this command.
        // 这种情况仍然可以认为src加载成功,source blocks与期待的匹配,命令可以执行
        return 0;
    }

    // 这种情况下, 如果source blocks和target blocks没有重叠,或者上面的LoadStash读取失败
	// 说明确实遇到了与期望不匹配的数据,更新不能继续,这时将params->isunresumable标记为1,函数返回-1表示失败
    // Valid source data not available, update cannot be resumed
    fprintf(stderr, "partition has unexpected contents\n");
    params.isunresumable = true;

    return -1;
}

// V1:move [src rangeset] [tgt rangeset] copy data from source blocks to target blocks (no patch needed; rangesets are the same size)
// move 2,545836,545840 2,545500,545504
// move b569d4f018e1cdda840f427eddc08a57b93d8c2e(sha1加密值,长度为40位) 2,545836,545840 4 2,545500,545504
// sha256--64 sha512--128
// 处理system.transfer.list中的move命令
static int PerformCommandMove(CommandParameters& params) {
    size_t blocks = 0;
    bool overlap = false;
    int status = 0;
    RangeSet tgt;

    // 执行LoadSrcTgtVersion1或LoadSrcTgtVersion2后,tgt就会保存target的block range信息
    //对于LoadSrcTgtVersion1,LoadSrcTgtVersion2,LoadSrcTgtVersion3, 这三个函数总体上都是将src或stash中的内容复制到内存中开辟的一段buffer中(params->buffer)
    //都不涉及之后的写入操作, 写入操作在之后根据params->canwrite来选择执行. 对于block_image_verify, params->canwrite为0,因此block_image_verify在执行move时就不会写入
    if (params.version == 1) {
        status = LoadSrcTgtVersion1(params, tgt, blocks, params.buffer, params.fd);
    } else if (params.version == 2) {
        status = LoadSrcTgtVersion2(params, tgt, blocks, params.buffer, params.fd,
                params.stashbase, nullptr);
    } else if (params.version >= 3) {
        status = LoadSrcTgtVersion3(params, tgt, blocks, true, overlap);
    }

    if (status == -1) {
        fprintf(stderr, "failed to read blocks for move\n");
        return -1;
    }

    if (status == 0) {
        params.foundwrites = true;
    } else if (params.foundwrites) {
        fprintf(stderr, "warning: commands executed out of order [%s]\n", params.cmdname);
    }

    if (params.canwrite) {
        if (status == 0) {
            fprintf(stderr, "  moving %zu blocks\n", blocks);

             //从blockdev_filename->data中取偏移,将buffer中的内容写入blockdev_filename->data
            if (WriteBlocks(tgt, params.buffer, params.fd) == -1) {
                return -1;
            }
        } else {
            fprintf(stderr, "skipping %zu already moved blocks\n", blocks);
        }

    }

    if (!params.freestash.empty()) {
        FreeStash(params.stashbase, params.freestash);
        params.freestash.clear();
    }

	// params->written在 for (line = strtok_r(NULL, "\n", &linesave)循环外面开始前初始化为0
	// 这里每执行完一次move,就累积这个move指令写入的block个数到params->written
    params.written += tgt.size;

    return 0;
}

// V2:stash <stash_id> <src_range> (version 2 only) load the given source range and stash the data in the given slot of the stash table.
// 每个stash命令的stash_id在后面的bsdiff或imgdiff的<[stash_id:stash_range] ...>部分中一定会再出现,
// 这时bsdiff或imgdiff会将每一个解析到的[stash_id:stash_range],从stash table指向的内存中加载到buffer中
// V2版只是完全将stash数据加载到内存中,STASH_DIRECTORY_BASE "/cache/recovery"在V3中引入
//stash 379e95f9e04037974674f92db25ce81576d85e64 2,268210,268211
// stash命令在v2开始出现
// V3版本: stash e271f3b2e779da7fb8374624b87bb0137b8a697a 2,544916,544917
static int PerformCommandStash(CommandParameters& params) {
    return SaveStash(params, params.stashbase, params.buffer, params.fd,
            (params.version >= 3));
}

static int PerformCommandFree(CommandParameters& params) {
    // <stash_id>
    if (params.cpos >= params.tokens.size()) {
        fprintf(stderr, "missing stash id in free command\n");
        return -1;
    }

    const std::string& id = params.tokens[params.cpos++];

    // 对于BlockImageVerifyFn, params->canwrite为0,因此不会删除/cache/recovery/{hash值} 下暂存的文件
    // 在performBlockImageUpdate中,CreateStash中如果没有判断没有stash就创建出stash,返回>0.如果已经存在stash返回0
    if (!params.canwrite && stash_map.find(id) != stash_map.end()) {
        stash_map.erase(id);
        return 0;
    }

    // 因此在执行free命令时, 如果之前已经创建了stash,就删除.如果stash本身就存在,对于verify不删除,对于update删除
    if (params.createdstash || params.canwrite) {
        return FreeStash(params.stashbase, id);
    }

    return 0;
}

// V1:zero [rangeset] fill the indicated blocks with zeros
// V1:erase [rangeset] mark the given blocks as empty
//处理zero, 如果定义了DEBUG_ERASE为1, 这时erase mean fill the region with zeroes, 和zero的行为实际一样
//zero //30,32770,32825,32827,33307,65535,65536,65538,66018,98303,98304,98306,98361,98363,98843,131071,131072,131074,131554,162907,163840,163842,16///3897,163899,164379,196607,196608,196610,197090,215039,215040
static int PerformCommandZero(CommandParameters& params) {

    if (params.cpos >= params.tokens.size()) {
        fprintf(stderr, "missing target blocks for zero\n");
        return -1;
    }

    RangeSet tgt;
    // 将word所有信息解析,保存到tgt结构体中.
    parse_range(params.tokens[params.cpos++], tgt);

    // tgt->size = 30个block编号组成的15个范围的 (右边-左边) 之和
    fprintf(stderr, "  zeroing %zu blocks\n", tgt.size);

    //调用allocate, 分配BLOCKSIZE大小的内存给buffer,buffer_alloc保存实际分配成功的内存大小
    allocate(BLOCKSIZE, params.buffer);
    //将buffer指向的BLOCKSIZE大小的这段内存全部写为0
    memset(params.buffer.data(), 0, BLOCKSIZE);

    if (params.canwrite) {
        //调用check_lseek取得15个block区间每个范围的左边
        for (size_t i = 0; i < tgt.count; ++i) {
            off64_t offset = static_cast<off64_t>(tgt.pos[i * 2]) * BLOCKSIZE;
            size_t size = (tgt.pos[i * 2 + 1] - tgt.pos[i * 2]) * BLOCKSIZE;
            if (!discard_blocks(params.fd, offset, size)) {
                return -1;
            }

            if (!check_lseek(params.fd, offset, SEEK_SET)) {
                return -1;
            }

            // 调用writeblock,向每个block区间写入 这个区间长度 次,每次将大小为BLOCKSIZE的内存块buffer写入到fd
            for (size_t j = tgt.pos[i * 2]; j < tgt.pos[i * 2 + 1]; ++j) {
                // 由于buffer指向的内存都是0, 因此实现了填0操作.
                if (write_all(params.fd, params.buffer, BLOCKSIZE) == -1) {
                    return -1;
                }
            }
        }
    }

    if (params.cmdname[0] == 'z') {
        // 对于zero命令还要把一共填0的block的数目累加, 计算 total_blocks已经处理 的百分比
        // Update only for the zero command, as the erase command will call
        // this if DEBUG_ERASE is defined.
        params.written += tgt.size;
    }

    return 0;
}

// V1:new [rangeset] - fill the blocks with data read from the new_data file
// 将rangeset代表的xx个block区间内的所有block,用从system.new.dat中解压出来的数据填充
// system.new.dat中保存的是system分区新版本相对于旧版本完全新增的文件 system.patch.dat中保存的是
//new //30,0,32770,32825,32827,33307,65535,65536,65538,66018,98303,98304,98306,98361,98363,98843,131071,131072,131074,131554,162907,163840,163842,163897,163899,164379,196607,//196608,196610,197090,215039
//$ file system.new.dat
// system.new.dat: Linux rev 1.0 ext2 filesystem data, UUID=da594c53-9beb-f85c-85c5-cedf76546f7a, volume name "system" (extents) (large files)
static int PerformCommandNew(CommandParameters& params) {

    if (params.cpos >= params.tokens.size()) {
        fprintf(stderr, "missing target blocks for new\n");
        return -1;
    }

    RangeSet tgt;
    // tgt保存30后所有信息
    parse_range(params.tokens[params.cpos++], tgt);

    if (params.canwrite) {
        fprintf(stderr, " writing %zu blocks of new data\n", tgt.size);

        RangeSinkState rss(tgt);
        rss.fd = params.fd;
        rss.p_block = 0;
        // p_remain保存每个block区间block个数
        rss.p_remain = (tgt.pos[1] - tgt.pos[0]) * BLOCKSIZE;

        off64_t offset = static_cast<off64_t>(tgt.pos[0]) * BLOCKSIZE;
        if (!discard_blocks(params.fd, offset, tgt.size * BLOCKSIZE)) {
            return -1;
        }

        // 设置要写入的偏移位置
        if (!check_lseek(params.fd, offset, SEEK_SET)) {
            return -1;
        }

        // 在new_data_thread子线程中真正完成system.new.dat的解压和把其中数据写入systen分区操作
        pthread_mutex_lock(&params.nti.mu);
        params.nti.rss = &rss;
        pthread_cond_broadcast(&params.nti.cv);

        while (params.nti.rss) {
            pthread_cond_wait(&params.nti.cv, &params.nti.mu);
        }

        pthread_mutex_unlock(&params.nti.mu);
    }

    // move,zero,new,imgdiff,bsdiff都要统计实际写入flash的block个数,erase不同统计
    // 一条命令执行完后统计一次,而不是一条命令内的每个block都逐一统计
    params.written += tgt.size;

    return 0;
}

// V1:bsdiff/imgdiff patchstart patchlen [src rangeset] [tgt rangeset]
// read the source blocks, apply a patch, write result to target blocks.  bsdiff or imgdiff specifies the type of patch. 
// bsdiff 0(patch_offset) 35581(patch_len) 2,367217,368194(src_range) 2,367217,368196(tgt_range)
// imgdiff 134034(patch_offset) 2022(patch_len) 2,40903,41035(src_range) 132 2,40904,41036(tgt_range)	
// V2:bsdiff/imgdiff <patchstart> <patchlen> <tgt_range> <src_block_count> <src_range> (loads data from source image only)
//    bsdiff/imgdiff <patchstart> <patchlen> <tgt_range> <src_block_count> - <[stash_id:stash_range] ...> (loads data from stashes only)
//    bsdiff/imgdiff <patchstart> <patchlen> <tgt_range> <src_block_count> <src_range> <src_loc> <[stash_id:stash_range] ...>  (loads data from both source image and stashes)

// V3:bsdiff/imgdiff <patchstart> <patchlen> <onehash> <tgt_range> <src_block_count> <src_range> (loads data from source image only)
//    bsdiff/imgdiff <patchstart> <patchlen> <onehash> <tgt_range> <src_block_count> - <[stash_id:stash_range] ...> (loads data from stashes only)
//    bsdiff/imgdiff <patchstart> <patchlen> <onehash> <tgt_range> <src_block_count> <src_range> <src_loc> <[stash_id:stash_range] ...>  (loads data from both source image and stashes)
// read the source blocks, apply a patch (or not in the case of move), write result to target blocks.
// bsdiff 0(patch_offset) 35581(patch_len) 67a63498a1293c14e23768bf7200348b8837e949 9c06e7e0277dee8c98e9a8b2a10d8649f6cfb3b0 2,367217,368194 979 2,367217,368196
// imgdiff 134034 2022 192e81959ac1985b1d90962faae1286029d4f39e 021c103903aa2da3ef222e1da5bdccdee287d1c3 2,40903,41035 132 2,40904,41036
static int PerformCommandDiff(CommandParameters& params) {

    // <offset> <length>
    // params->cpos执行的就是transfer.list中命令名后面的所有字符串
    if (params.cpos + 1 >= params.tokens.size()) {
        fprintf(stderr, "missing patch offset or length for %s\n", params.cmdname);
        return -1;
    }

    size_t offset;
    // 解析得到bsdiff/imgdiff命令的  patch offset参数
    if (!android::base::ParseUint(params.tokens[params.cpos++].c_str(), &offset)) {
        fprintf(stderr, "invalid patch offset\n");
        return -1;
    }

    size_t len;
    // 解析得到bsdiff/imgdiff命令的  patch length参数
    if (!android::base::ParseUint(params.tokens[params.cpos++].c_str(), &len)) {
        fprintf(stderr, "invalid patch offset\n");
        return -1;
    }

    RangeSet tgt;
    size_t blocks = 0;
    bool overlap = false;
    int status = 0;
    if (params.version == 1) {
        status = LoadSrcTgtVersion1(params, tgt, blocks, params.buffer, params.fd);
    } else if (params.version == 2) {
        status = LoadSrcTgtVersion2(params, tgt, blocks, params.buffer, params.fd,
                params.stashbase, nullptr);
    } else if (params.version >= 3) {
        status = LoadSrcTgtVersion3(params, tgt, blocks, false, overlap);
    }

    if (status == -1) {
        fprintf(stderr, "failed to read blocks for diff\n");
        return -1;
    }

    if (status == 0) {
        params.foundwrites = true;
    } else if (params.foundwrites) {
        fprintf(stderr, "warning: commands executed out of order [%s]\n", params.cmdname);
    }

    if (params.canwrite) {
        if (status == 0) {
            fprintf(stderr, "patching %zu blocks to %zu\n", blocks, tgt.size);

            Value patch_value;
            patch_value.type = VAL_BLOB;
            patch_value.size = len;
            // patch_start是ota压缩包中system.patch.dat文件在内存中的绝对地址, patch_offset是imgdiff或bsdiff命令要打的补丁数据在system.patch.dat中的相对地址
            // 因此patch_value.data指向的就是此补丁数据在system.patch.dat中的绝对地址
            patch_value.data = (char*) (params.patch_start + offset);

            RangeSinkState rss(tgt);
            rss.fd = params.fd;
            rss.p_block = 0;
            rss.p_remain = (tgt.pos[1] - tgt.pos[0]) * BLOCKSIZE;

            off64_t offset = static_cast<off64_t>(tgt.pos[0]) * BLOCKSIZE;
            if (!discard_blocks(params.fd, offset, rss.p_remain)) {
                return -1;
            }

            if (!check_lseek(params.fd, offset, SEEK_SET)) {
                return -1;
            }

            if (params.cmdname[0] == 'i') {      // imgdiff
                if (ApplyImagePatch(params.buffer.data(), blocks * BLOCKSIZE, &patch_value,
                        &RangeSinkWrite, &rss, nullptr, nullptr) != 0) {
                    fprintf(stderr, "Failed to apply image patch.\n");
                    return -1;
                }
            } else {
                if (ApplyBSDiffPatch(params.buffer.data(), blocks * BLOCKSIZE, &patch_value,
                        0, &RangeSinkWrite, &rss, nullptr) != 0) {
                    fprintf(stderr, "Failed to apply bsdiff patch.\n");
                    return -1;
                }
            }

            // We expect the output of the patcher to fill the tgt ranges exactly.
            // 打完pathc后rss.p_block就是新生成的目标大小
            if (rss.p_block != tgt.count || rss.p_remain != 0) {
                 //对于ApplyImagePatch或ApplyBSDiffPatch,都是在RangeSinkWrite中完成rss->p_remain-=write_now 正常情况下rss.p_remain应为0
                fprintf(stderr, "range sink underrun?\n");
            }
        } else {
			// status为1才能执行到这里,这种情况说明tgt与tgt hash匹配,命令不用执行
            fprintf(stderr, "skipping %zu blocks already patched to %zu [%s]\n",
                blocks, tgt.size, params.cmdline);
        }
    }

    if (!params.freestash.empty()) {
        FreeStash(params.stashbase, params.freestash);
        params.freestash.clear();
    }

    params.written += tgt.size;

    return 0;
}

//v1 v2:erase 14,546363,556544,557570,589312,590338,622080,623106,654848,655874,687616,688642,720384,721410,753152
//v3:erase 18,465883,491008,492034,523776,524802,556544,557570,589312,590338,622080,623106,654848,655874,687616,688642,720384,721410,753152
static int PerformCommandErase(CommandParameters& params) {
    //DEBUG_ERASE 默认为0, 这时执行system.transfer.list中的erase命令时
    if (DEBUG_ERASE) {
        return PerformCommandZero(params);
    }

    struct stat sb;
    //先根据open(blockdev_filename->data)读到的fd 判断target是不是块设备
    if (fstat(params.fd, &sb) == -1) {
        fprintf(stderr, "failed to fstat device to erase: %s\n", strerror(errno));
        return -1;
    }

    //先根据open(blockdev_filename->data)读到的fd 判断target是不是块设备
    if (!S_ISBLK(sb.st_mode)) {
        fprintf(stderr, "not a block device; skipping erase\n");
        return -1;
    }

    if (params.cpos >= params.tokens.size()) {
        fprintf(stderr, "missing target blocks for erase\n");
        return -1;
    }

    RangeSet tgt;
    // range 14,546363,....,753152
    parse_range(params.tokens[params.cpos++], tgt);

    if (params.canwrite) {
        fprintf(stderr, " erasing %zu blocks\n", tgt.size);

        for (size_t i = 0; i < tgt.count; ++i) {
            uint64_t blocks[2];
            // offset in bytes
            // blocks[0] 每个区间的起始位置
            blocks[0] = tgt.pos[i * 2] * (uint64_t) BLOCKSIZE;
            // length in bytes
            // blocks[1] 每个区间的长度
            blocks[1] = (tgt.pos[i * 2 + 1] - tgt.pos[i * 2]) * (uint64_t) BLOCKSIZE;

			// #define BLKDISCARD _IO(0x12,119)blkdiscard is used to discard device sectors.This is useful for solid-state drivers (SSDs) and thinly-provisioned storage 
			// 调用ioctl屏蔽range描述的块组区间
            if (ioctl(params.fd, BLKDISCARD, &blocks) == -1) {
                fprintf(stderr, "BLKDISCARD ioctl failed: %s\n", strerror(errno));
                return -1;
            }
        }
    }

    return 0;
}

// Definitions for transfer list command functions
typedef int (*CommandFunction)(CommandParameters&);

struct Command {
    const char* name;
    CommandFunction f;
};

// CompareCommands and CompareCommandNames are for the hash table

static int CompareCommands(const void* c1, const void* c2) {
    return strcmp(((const Command*) c1)->name, ((const Command*) c2)->name);
}

static int CompareCommandNames(const void* c1, const void* c2) {
    return strcmp(((const Command*) c1)->name, (const char*) c2);
}

// HashString is used to hash command names for the hash table

// 输出为一个字符串,输出为一个int型的hash值
//在用到hash进行管理的数据结构中，比如hashmap，hash值（key）存在的目的是加速键值对的查找，key的作用是为了将元素适当地放在各个桶里，对于抗碰撞的要求没有那么高。换句话说，hash出来的key，只要保证value大致均匀的放在不同的桶里就可以了
static unsigned int HashString(const char *s) {
    unsigned int hash = 0;
    if (s) {
        while (*s) {
            hash = hash * 33 + *s++;
        }
    }
    return hash;
}

// args:
//    - block device (or file) to modify in-place
//    - transfer list (blob)
//    - new data stream (filename within package.zip)
//    - patch stream (filename within package.zip, must be uncompressed)

//in-place操作，意思是所有的操作都是”就地“操作，不允许进行移动，或者称作 原位操作，即不允许使用临时变量。
//block_image_update("/dev/block/platform/soc.0/f9824900.sdhci/by-name/system", package_extract_file("system.transfer.list"), "system.new.dat", "system.patch.dat");
// argc就是block_image_update或block_image_verify的参数个数,argv数组的每个值就是block_image_update或block_image_verify的各个参数
// command就是block_image_update或block_image_verify支持的命令数组
// cmdcount就是block_image_update或block_image_verify支持的命令的个数
static Value* PerformBlockImageUpdate(const char* name, State* state, int /* argc */, Expr* argv[],
        const Command* commands, size_t cmdcount, bool dryrun) {
    CommandParameters params;
    memset(&params, 0, sizeof(params));
    params.canwrite = !dryrun;

    fprintf(stderr, "performing %s\n", dryrun ? "verification" : "update");
    if (state->is_retry) {
        is_retry = true;
        fprintf(stderr, "This update is a retry.\n");
    }

    Value* blockdev_filename = nullptr;
    Value* transfer_list_value = nullptr;
    Value* new_data_fn = nullptr;
    Value* patch_data_fn = nullptr;
    //ReadValueArgs取得脚本中的/dev/block/bootdevice/by-name/system，package_extract_file("system.transfer.list"),system.new.dat", "system.patch.dat"这四个参数，赋值给blockdev_filename ，transfer_list_value， new_data_fn，patch_data_fn
    // 因为block_image_update中有类似package_extract_file("system.transfer.list")这种还需要执行才能得到返回值的函数
    // 在ReadValueArgs中利用va_list等C语言的可变参数宏，将block_image_update的四个输入参数"/dev/block/bootdevice/by-name/system", package_extract_file("system.transfer.list"), "system.new.dat", "system.patch.dat"，分别赋值给blockdev_filename，transfer_list_value，new_data_fn，patch_data_fn
    // ReadValueArgs成功执行后:
    // blockdev_filename -- /dev/block/bootdevice/by-name/system
    // transfer_list_value -- system.transfer.list文件内容
    // new_data_fn -- system.new.dat, new_data_fn -- system.patch.dat
    if (ReadValueArgs(state, argv, 4, &blockdev_filename, &transfer_list_value,
            &new_data_fn, &patch_data_fn) < 0) {
        return StringValue(strdup(""));
    }
    std::unique_ptr<Value, decltype(&FreeValue)> blockdev_filename_holder(blockdev_filename,
            FreeValue);
    std::unique_ptr<Value, decltype(&FreeValue)> transfer_list_value_holder(transfer_list_value,
            FreeValue);
    std::unique_ptr<Value, decltype(&FreeValue)> new_data_fn_holder(new_data_fn, FreeValue);
    std::unique_ptr<Value, decltype(&FreeValue)> patch_data_fn_holder(patch_data_fn, FreeValue);

    if (blockdev_filename->type != VAL_STRING) {
        //在BlockImageUpdateFn函数中name就是block_image_update,这个错误log的意思就是block_image_update的blockdev_filename参数必须是string类型
        ErrorAbort(state, kArgsParsingFailure, "blockdev_filename argument to %s must be string",
                   name);
        return StringValue(strdup(""));
    }
    // 在package_extract_file("system.transfer.list"),中将type设为了VAL_BLOB
	// BLOB (binary large object)，二进制大对象，是一个可以存储二进制文件的容器 //BLOB是一个大文件，典型的BLOB是一张图片或一个声音文件，由于它们的尺寸，必须使用特殊的方式来处理（例如：上传、下载或者存放到一个数据库）
    if (transfer_list_value->type != VAL_BLOB) {
        ErrorAbort(state, kArgsParsingFailure, "transfer_list argument to %s must be blob", name);
        return StringValue(strdup(""));
    }
    if (new_data_fn->type != VAL_STRING) {
        ErrorAbort(state, kArgsParsingFailure, "new_data_fn argument to %s must be string", name);
        return StringValue(strdup(""));
    }
    if (patch_data_fn->type != VAL_STRING) {
        ErrorAbort(state, kArgsParsingFailure, "patch_data_fn argument to %s must be string",
                   name);
        return StringValue(strdup(""));
    }

    // 这里的ui是updater info的含义，而不是user interface
    // state.cookie = &updater_info;updater_info.cmd_pipe = cmd_pipe; updater_info.package_zip = &za;updater_info.version = atoi(version);updater_info.package_zip_addr = map.addr;
    // updater_info.package_zip_len = map.length;
    UpdaterInfo* ui = reinterpret_cast<UpdaterInfo*>(state->cookie);

    if (ui == nullptr) {
        return StringValue(strdup(""));
    }

    // 升级时updater子进程通过cmd_pipe将progress进度传给recovery进程
    FILE* cmd_pipe = ui->cmd_pipe;
    // za就代表整个zip格式的ota包
    ZipArchive* za = ui->package_zip;

    if (cmd_pipe == nullptr || za == nullptr) {
        return StringValue(strdup(""));
    }

    //patch_data_fn->data指向的是“system.patch.dat”这段字符串，而不是 system.patch.dat这个文件的内容，
    //因此patch_entry就代表内存中的zip安装包中的system.patch.dat这一项
    // 从ota zip包中找到system.patch.dat文件
    const ZipEntry* patch_entry = mzFindZipEntry(za, patch_data_fn->data);
    if (patch_entry == nullptr) {
        fprintf(stderr, "%s(): no file \"%s\" in package", name, patch_data_fn->data);
        return StringValue(strdup(""));
    }

    //内存中ota zip包起始地址+system.patch.dat在zip包中的相对偏移,得到system.patch.dat文件在内存中地址
    // 计算出patch_entry的起始地址patch_start，因为注释中说patch stream must be uncompressed
    // patch_start在下面循环中执行bsdiff或imgdiff命令中会用到
    // package_zip_addr + mzGetZipEntryOffset(patch_entry) zip安装包在内存中的绝对地址+ system.patch.dat在zip包内的相对偏移地址
    // 因此patch_start就代表压缩包中system.patch.dat文件在内存中的绝对地址
    params.patch_start = ui->package_zip_addr + mzGetZipEntryOffset(patch_entry);
    // new_data_fn->data指向字符串"system.new.dat",从ota zip包中找到system.new.dat文件
    //new_data_fn->data指向的数据是“system.new.dat”，而不是system.new.dat这个文件的内容
    //new_entry就代表内存中的zip安装包中的system.new.dat这一项
    const ZipEntry* new_entry = mzFindZipEntry(za, new_data_fn->data);
    if (new_entry == nullptr) {
        fprintf(stderr, "%s(): no file \"%s\" in package", name, new_data_fn->data);
        return StringValue(strdup(""));
    }

    // 打开/dev/block/bootdevice/by-name/system等
    params.fd = TEMP_FAILURE_RETRY(open(blockdev_filename->data, O_RDWR));
    unique_fd fd_holder(params.fd);

    if (params.fd == -1) {
        fprintf(stderr, "open \"%s\" failed: %s\n", blockdev_filename->data, strerror(errno));
        return StringValue(strdup(""));
    }

    // 对于 block_image_verify,canwrite为0
    if (params.canwrite) {
        // block_image_update才会执行这些
        // nti.za就代表整个zip格式的ota包
        params.nti.za = za;
        // 这里就将ota zip包中的system.new.dat传给了nti.entry
        params.nti.entry = new_entry;

        //互斥锁的初始化
        pthread_mutex_init(&params.nti.mu, nullptr);
        //创建一个条件变量，cv就是condition value的意思
	    //extern int pthread_cond_init __P ((pthread_cond_t *__cond,__const pthread_condattr_t *__cond_attr)); 其中cond是一个指向结构pthread_cond_t的指针，cond_attr是一个指向结构pthread_condattr_t的指 针。结构 pthread_condattr_t是条件变量的属性结构，和互斥锁一样我 们可以用它来设置条件变量是进程内可用还是进程间可用，默认值是 PTHREAD_ PROCESS_PRIVATE，即此条件变量被同一进程内的各个线程使用
        pthread_cond_init(&params.nti.cv, nullptr);
        pthread_attr_t attr;
        //线程具有属性,用pthread_attr_t表示,在对该结构进行处理之前必须进行初始化，我们用pthread_attr_init函数对其初始化，用pthread_attr_destroy对其去除初始化
        pthread_attr_init(&attr);
        //pthread_attr_setdetachstate 修改线程的分离状态属性，可以使用pthread_attr_setdetachstate函数把线程属性detachstate设置为下面的两个合法值之一：设置为PTHREAD_CREATE_DETACHED,以分离状态启动线程；或者设置为PTHREAD_CREATE_JOINABLE,正常启动线程。线程的分离状态决定一个线程以什么样的方式来终止自己。在默认情况下线程是非分离状态的，这种情况下，原有的线程等待创建的线程结束。只有当pthread_join（）函数返回时，创建的线程才算终止，才能释放自己占用的系统资源。
        pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);

        //pthread_create的四个参数：1指向线程标识符的指针 2 设置线程属性 3 线程运行函数的起始地址 4 运行函数的参数。
        // pthread_create将会创建线程,在线程创建以后，就开始运行相关的线程函数
        // 因此在BlockImageUpdateFn中将会创建出一个线程,
        //线程标识符--new_data_thread,   //线程属性attr设置为了PTHREAD_CREATE_JOINABLE,代表非分离线程,非分离的线程终止时，其线程ID和退出状态将保留，直到另外一个线程调用pthread_join.
        // 线程函数的起始地址, 这里就是执行unzip_new_data函数
        //nti--传给unzip_new_data函数的参数
        // 创建名为调用unzip_new_data的现场,在其中执行unzip_new_data,在unzip_new_data中调用mzProcessZipEntryContents完成对system.new.data文件的解压
        int error = pthread_create(&params.thread, &attr, unzip_new_data, &params.nti);
        if (error != 0) {
            fprintf(stderr, "pthread_create failed: %s\n", strerror(error));
            return StringValue(strdup(""));
        }
    }

    // Copy all the lines in transfer_list_value into std::string for
    // processing.
    const std::string transfer_list(transfer_list_value->data, transfer_list_value->size);
    std::vector<std::string> lines = android::base::Split(transfer_list, "\n");
    if (lines.size() < 2) {
        ErrorAbort(state, kArgsParsingFailure, "too few lines in the transfer list [%zd]\n",
                   lines.size());
        return StringValue(strdup(""));
    }

    // First line in transfer list is the version number
    // line用于保存transfer.list文件的每一单行
    // 读取transfer.list文件的第1行
    if (!android::base::ParseInt(lines[0].c_str(), &params.version, 1, 4)) {
        // version保存transfer.list文件第一行版本号
        // recovery 5.0 lollipop-erlease对应的api是1
        // d83e4f15890ac6ebe0d61924bd224eb1ae8565ad support for version 2 of block image diffs Change-Id: I4559bfd76d5403859637aeac832f3a5e9e13b63a 开始新增V2
        // commit 90221205a3e58f2a198faa838088dc7bc7c9c752 Support resuming block based OTAs Change-Id: I1e752464134aeb2d396946348e6041acabe13942 开始新增V3
        fprintf(stderr, "unexpected transfer list version [%s]\n", lines[0].c_str());
        return StringValue(strdup(""));
    }

    fprintf(stderr, "blockimg version is %d\n", params.version);

    // Second line in transfer list is the total number of blocks we expect to write
    int total_blocks;
    // 读取transfer.list文件的第2行
    if (!android::base::ParseInt(lines[1].c_str(), &total_blocks, 0)) {
        ErrorAbort(state, kArgsParsingFailure, "unexpected block count [%s]\n", lines[1].c_str());
        return StringValue(strdup(""));
    }

    if (total_blocks == 0) {
        return StringValue(strdup("t"));
    }

    size_t start = 2;
    if (params.version >= 2) {
        if (lines.size() < 4) {
            ErrorAbort(state, kArgsParsingFailure, "too few lines in the transfer list [%zu]\n",
                       lines.size());
            return StringValue(strdup(""));
        }

        // Third line is how many stash entries are needed simultaneously
        // 对于system.transfer.list文件的第三行,如果版本号>=2,第三行就是同时需要的stash entry
        // transfer.list从V2开始,第3行为同时并存的stash文件数
        fprintf(stderr, "maximum stash entries %s\n", lines[2].c_str());

        // Fourth line is the maximum number of blocks that will be stashed simultaneously
        // transfer.list从V2开始,第4行为最大stash文件所占用的block空间数.stash_max_blocks可用于检测是否有足够多可用的内存或零散磁盘空间
        int stash_max_blocks;
        if (!android::base::ParseInt(lines[3].c_str(), &stash_max_blocks, 0)) {
            ErrorAbort(state, kArgsParsingFailure, "unexpected maximum stash blocks [%s]\n",
                       lines[3].c_str());
            return StringValue(strdup(""));
        }

        //stash在 版本号>=2 引入,因此要首先在 /cache/recovery/{base}/文件夹 下创建出足够空间
        int res = CreateStash(state, stash_max_blocks, blockdev_filename->data, params.stashbase);
        if (res == -1) {
            return StringValue(strdup(""));
        }

        params.createdstash = res;

        start += 2;
    }

    // Build a hash table of the available commands
    // cmdcount对于BlockImageVerifyFn 和 BlockImageUpdateF都是8,第二个参数也都是NULL
    HashTable* cmdht = mzHashTableCreate(cmdcount, nullptr);
    std::unique_ptr<HashTable, decltype(&mzHashTableFree)> cmdht_holder(cmdht, mzHashTableFree);

    for (size_t i = 0; i < cmdcount; ++i) {
        unsigned int cmdhash = HashString(commands[i].name);
        //将Verify或Update支持的命令写入hash表中
        mzHashTableLookup(cmdht, cmdhash, (void*) &commands[i], CompareCommands, true);
    }

    int rc = -1;

    // Subsequent lines are all individual transfer commands
    // 第四行后面的各行都是独立的命令,在这个for循环中依次读取并执行每行命令
    for (auto it = lines.cbegin() + start; it != lines.cend(); it++) {
        const std::string& line_str(*it);
        if (line_str.empty()) {
            continue;
        }

        params.tokens = android::base::Split(line_str, " ");
        params.cpos = 0;
        // params.cmdname保存每行开头的命令名称
        params.cmdname = params.tokens[params.cpos++].c_str();
        params.cmdline = line_str.c_str();

        unsigned int cmdhash = HashString(params.cmdname);
        // 在Verify或Update保存的hash表中查找这行开头的命令是否支持
        const Command* cmd = reinterpret_cast<const Command*>(mzHashTableLookup(cmdht, cmdhash,
                const_cast<char*>(params.cmdname), CompareCommandNames,
                false));

        if (cmd == nullptr) {
            fprintf(stderr, "unexpected command [%s]\n", params.cmdname);
            goto pbiudone;
        }

		// 对于BlockImageVerifyFn,如果传入的commands数组中name对应的操作函数为NULL,则这里cmd->f就为NULL,所以BlockImageVerifyFn在解析system.transfer.list时就会跳过不支持的命令
		// 对于BlockImageVerifyFn和BlockImageUpdateFn支持的命令,cmd->f就不为NULL,因此cmd->f(&params)就是在这个for循环中执行每行支持的命令
        if (cmd->f != nullptr && cmd->f(params) == -1) {
            fprintf(stderr, "failed to execute command [%s]\n", line_str.c_str());
            goto pbiudone;
        }

        if (params.canwrite) {
            // 调用pthread_join等待子线程new_data_thread的结束
            if (ota_fsync(params.fd) == -1) {
                failure_type = kFsyncFailure;
                fprintf(stderr, "fsync failed: %s\n", strerror(errno));
                goto pbiudone;
            }
            fprintf(cmd_pipe, "set_progress %.4f\n", (double) params.written / total_blocks);
            fflush(cmd_pipe);
        }
    }

    if (params.canwrite) {
        pthread_join(params.thread, nullptr);

        // blocks_so_far为实际写入的block个数,total_blocks为升级脚本第二行计划写入的block个数.正常情况下两者相等.
        fprintf(stderr, "wrote %zu blocks; expected %d\n", params.written, total_blocks);
        fprintf(stderr, "stashed %zu blocks\n", params.stashed);
        // 这是buffer_alloc的大小就是执行transfer.list中命令过程中最大分配的一段内存大小
        fprintf(stderr, "max alloc needed was %zu\n", params.buffer.size());

        const char* partition = strrchr(blockdev_filename->data, '/');
        if (partition != nullptr && *(partition+1) != 0) {
            fprintf(cmd_pipe, "log bytes_written_%s: %zu\n", partition + 1,
                    params.written * BLOCKSIZE);
            fprintf(cmd_pipe, "log bytes_stashed_%s: %zu\n", partition + 1,
                    params.stashed * BLOCKSIZE);
            fflush(cmd_pipe);
        }
        // Delete stash only after successfully completing the update, as it
        // may contain blocks needed to complete the update later.
        DeleteStash(params.stashbase);
    } else {
        fprintf(stderr, "verified partition contents; update may be resumed\n");
    }

    rc = 0;

pbiudone:
    if (ota_fsync(params.fd) == -1) {
        failure_type = kFsyncFailure;
        fprintf(stderr, "fsync failed: %s\n", strerror(errno));
    }
    // params.fd will be automatically closed because of the fd_holder above.

    // Only delete the stash if the update cannot be resumed, or it's
    // a verification run and we created the stash.
    if (params.isunresumable || (!params.canwrite && params.createdstash)) {
        DeleteStash(params.stashbase);
    }

    if (failure_type != kNoCause && state->cause_code == kNoCause) {
        state->cause_code = failure_type;
    }

    return StringValue(rc == 0 ? strdup("t") : strdup(""));
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
//    erase [rangeset]
//      - mark the given blocks as empty
//
//    move <...>
//    bsdiff <patchstart> <patchlen> <...>
//    imgdiff <patchstart> <patchlen> <...>
//      - read the source blocks, apply a patch (or not in the
//        case of move), write result to target blocks.  bsdiff or
//        imgdiff specifies the type of patch; move means no patch
//        at all.
//
//        The format of <...> differs between versions 1 and 2;
//        see the LoadSrcTgtVersion{1,2}() functions for a
//        description of what's expected.
//
//    stash <stash_id> <src_range>
//      - (version 2+ only) load the given source range and stash
//        the data in the given slot of the stash table.
//
//    free <stash_id>
//      - (version 3+ only) free the given stash data.
//
// The creator of the transfer list will guarantee that no block
// is read (ie, used as the source for a patch or move) after it
// has been written.
//
// In version 2, the creator will guarantee that a given stash is
// loaded (with a stash command) before it's used in a
// move/bsdiff/imgdiff command.
// 创建transfer list时会保证 一个stash在stash命令中的加载 会放在被move/bsdiff/imgdiff命令使用此stash之前
// v2中,支持一个新命令stash, stash将从source img中读取的数据,保存到
// 分配的内存"stash table", 随后会 用stash table中刚存储的项去填充
// source data中丢失的字节位,因为这些字节位在执行move/bsdiff/imgdiff
// 时是不允许去读的
// 这会产生更小的升级包,因为我们可以通过把数据存储到别处然后以后使用的方式, 
// 来到达 按pieces是怎么更新的顺序 来组织
// 而不是一点都不使用 作为输入的数据来对系统打patch
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
//
// In version 3, commands that read data from the partition (i.e.
// move/bsdiff/imgdiff/stash) have one or more additional hashes
// before the range parameters, which are used to check if the
// command has already been completed and verify the integrity of
// the source data.
// 在V3中,需要从flash分区读取数据的命令(move/bsdiff/imgdiff/stash),
// 在range参数前有一个或多个hash值(sha1),这些hash值用于检查命令是否
// 已经完成,并且验证source data的完整性

//L上支持的命令bsdiff,erase,imgdiff,move,new,zero
//M上增加的命令:stash(v2新增),free(v3新增)
		
//block_image_verify("/dev/block/bootdevice/by-name/system", package_extract_file("system.transfer.list"), "system.new.dat", "system.patch.dat")
//block_image_verify("/dev/block/platform/soc.0/f9824900.sdhci/by-name/system", package_extract_file("system.transfer.list"), "system.new.dat", "system.patch.dat")
Value* BlockImageVerifyFn(const char* name, State* state, int argc, Expr* argv[]) {
    // Commands which are not tested are set to nullptr to skip them completely
    const Command commands[] = {
        { "bsdiff",     PerformCommandDiff  },
        { "erase",      nullptr             },
        { "free",       PerformCommandFree  },
        { "imgdiff",    PerformCommandDiff  },
        { "move",       PerformCommandMove  },
        { "new",        nullptr             },
        { "stash",      PerformCommandStash },
        { "zero",       nullptr             }
    };

    // Perform a dry run without writing to test if an update can proceed
    return PerformBlockImageUpdate(name, state, argc, argv, commands,
                sizeof(commands) / sizeof(commands[0]), true);
}

//block_image_update("/dev/block/platform/soc.0/f9824900.sdhci/by-name/system", package_extract_file("system.transfer.list"), "system.new.dat", "system.patch.dat");
//因此脚本中调用BlockImageUpdateFn时,传给BlockImageUpdateFn的argc是block_image_update的参数个数,
// argv数组的每个值就是block_image_update的各个参数
Value* BlockImageUpdateFn(const char* name, State* state, int argc, Expr* argv[]) {
    const Command commands[] = {
        { "bsdiff",     PerformCommandDiff  },
        { "erase",      PerformCommandErase },
        { "free",       PerformCommandFree  },
        { "imgdiff",    PerformCommandDiff  },
        { "move",       PerformCommandMove  },
        { "new",        PerformCommandNew   },
        { "stash",      PerformCommandStash },
        { "zero",       PerformCommandZero  }
    };

    return PerformBlockImageUpdate(name, state, argc, argv, commands,
                sizeof(commands) / sizeof(commands[0]), false);
}

//if (range_sha1("/dev/block/platform/mtk-msdc.0/11230000.msdc0/by-name/syst
//em", "72,1,32770,32929,32931,33439,65535,65536,65538,66046,98303,98304,98306,98465,98467,98975,131071,131072,131074,131582,163839,163840,163842,164001,164003,164511,196607,196608,196610,197118,22
//9375,229376,229378,229537,229539,230047,262143,262144,262146,262654,294911,294912,294914,295073,295075,295583,327679,327680,327682,328190,355086,360448,360450,393216,393218,425984,425986,458752,458754,491520,491522,524288,524290,557056,557058,589824,589826,622592,622594,623102,650190,650191,655320") == "3168346b9a857c0dd0e962e86032bf464a007957" || block_image_verify("/dev/block/platform/mtk-msdc.0/11230000.msdc0/by-name/system", package_extract_file("system.transfer.list"), "system.new.dat", "system.patch.dat")) then
Value* RangeSha1Fn(const char* name, State* state, int /* argc */, Expr* argv[]) {
    Value* blockdev_filename;
    Value* ranges;

    // 解析range_sha1的分区路径到blockdev_filename,解析区间范围参数到ranges
    if (ReadValueArgs(state, argv, 2, &blockdev_filename, &ranges) < 0) {
        return StringValue(strdup(""));
    }
    std::unique_ptr<Value, decltype(&FreeValue)> ranges_holder(ranges, FreeValue);
    std::unique_ptr<Value, decltype(&FreeValue)> blockdev_filename_holder(blockdev_filename,
            FreeValue);

    if (blockdev_filename->type != VAL_STRING) {
        ErrorAbort(state, kArgsParsingFailure, "blockdev_filename argument to %s must be string",
                   name);
        return StringValue(strdup(""));
    }
    if (ranges->type != VAL_STRING) {
        ErrorAbort(state, kArgsParsingFailure, "ranges argument to %s must be string", name);
        return StringValue(strdup(""));
    }

    // 打开/dev/block/platform/mtk-msdc.0/11230000.msdc0/by-name/system设备节点
    int fd = open(blockdev_filename->data, O_RDWR);
    unique_fd fd_holder(fd);
    if (fd < 0) {
        ErrorAbort(state, kFileOpenFailure, "open \"%s\" failed: %s", blockdev_filename->data,
                   strerror(errno));
        return StringValue(strdup(""));
    }

    // ranges->data指向"72,1,32770,32...",将这72个区间段解析后保存到rs
    RangeSet rs;
    parse_range(ranges->data, rs);

    SHA_CTX ctx;
    SHA1_Init(&ctx);

    // buffer大小刚好是1个block
    std::vector<uint8_t> buffer(BLOCKSIZE);
    // 在外层循环 block区间 的个数次,从而叠加积累每个区间
    // 在for循环中累计更新这72个区间的hash,累计完后一次性计算sha1
    for (size_t i = 0; i < rs.count; ++i) {
        if (!check_lseek(fd, (off64_t)rs.pos[i*2] * BLOCKSIZE, SEEK_SET)) {
            ErrorAbort(state, kLseekFailure, "failed to seek %s: %s", blockdev_filename->data,
                       strerror(errno));
            return StringValue(strdup(""));
        }

        // 这个for中更新每个区间内所有block的hash
        //在里层for循环中处理每个区间,一次读入一个block到buffer并更新ctx, 循环次数为这个block区间的大小
        for (size_t j = rs.pos[i*2]; j < rs.pos[i*2+1]; ++j) {
            //每循环一次读取1个block,并更新hash
            if (read_all(fd, buffer, BLOCKSIZE) == -1) {
                ErrorAbort(state, kFreadFailure, "failed to read %s: %s", blockdev_filename->data,
                        strerror(errno));
                return StringValue(strdup(""));
            }

            SHA1_Update(&ctx, buffer.data(), BLOCKSIZE);
        }
    }
    uint8_t digest[SHA_DIGEST_LENGTH];
    //计算所有block区间叠加起来的sha
    // digest就是最终这72个区间的sha1,range_sha1返回digest的值,在if中和3168346b9a857c0dd0e962e86032bf464a007957比较
    SHA1_Final(digest, &ctx);

    // 返回Value格式的sha, 返回的value的type字段为VAL_STRING
    return StringValue(strdup(print_sha1(digest).c_str()));
}

// This function checks if a device has been remounted R/W prior to an incremental
// OTA update. This is an common cause of update abortion. The function reads the
// 1st block of each partition and check for mounting time/count. It return string "t"
// if executes successfully and an empty string otherwise.

Value* CheckFirstBlockFn(const char* name, State* state, int argc, Expr* argv[]) {
    Value* arg_filename;

    if (ReadValueArgs(state, argv, 1, &arg_filename) < 0) {
        return nullptr;
    }
    std::unique_ptr<Value, decltype(&FreeValue)> filename(arg_filename, FreeValue);

    if (filename->type != VAL_STRING) {
        ErrorAbort(state, kArgsParsingFailure, "filename argument to %s must be string", name);
        return StringValue(strdup(""));
    }

    int fd = open(arg_filename->data, O_RDONLY);
    unique_fd fd_holder(fd);
    if (fd == -1) {
        ErrorAbort(state, kFileOpenFailure, "open \"%s\" failed: %s", arg_filename->data,
                   strerror(errno));
        return StringValue(strdup(""));
    }

    RangeSet blk0 {1 /*count*/, 1/*size*/, std::vector<size_t> {0, 1}/*position*/};
    std::vector<uint8_t> block0_buffer(BLOCKSIZE);

    if (ReadBlocks(blk0, block0_buffer, fd) == -1) {
        ErrorAbort(state, kFreadFailure, "failed to read %s: %s", arg_filename->data,
                strerror(errno));
        return StringValue(strdup(""));
    }

    // https://ext4.wiki.kernel.org/index.php/Ext4_Disk_Layout
    // Super block starts from block 0, offset 0x400
    //   0x2C: len32 Mount time
    //   0x30: len32 Write time
    //   0x34: len16 Number of mounts since the last fsck
    //   0x38: len16 Magic signature 0xEF53

    time_t mount_time = *reinterpret_cast<uint32_t*>(&block0_buffer[0x400+0x2C]);
    uint16_t mount_count = *reinterpret_cast<uint16_t*>(&block0_buffer[0x400+0x34]);

    if (mount_count > 0) {
        uiPrintf(state, "Device was remounted R/W %d times\n", mount_count);
        uiPrintf(state, "Last remount happened on %s", ctime(&mount_time));
    }

    return StringValue(strdup("t"));
}


Value* BlockImageRecoverFn(const char* name, State* state, int argc, Expr* argv[]) {
    Value* arg_filename;
    Value* arg_ranges;

    if (ReadValueArgs(state, argv, 2, &arg_filename, &arg_ranges) < 0) {
        return NULL;
    }

    std::unique_ptr<Value, decltype(&FreeValue)> filename(arg_filename, FreeValue);
    std::unique_ptr<Value, decltype(&FreeValue)> ranges(arg_ranges, FreeValue);

    if (filename->type != VAL_STRING) {
        ErrorAbort(state, kArgsParsingFailure, "filename argument to %s must be string", name);
        return StringValue(strdup(""));
    }
    if (ranges->type != VAL_STRING) {
        ErrorAbort(state, kArgsParsingFailure, "ranges argument to %s must be string", name);
        return StringValue(strdup(""));
    }

    // Output notice to log when recover is attempted
    fprintf(stderr, "%s image corrupted, attempting to recover...\n", filename->data);

    // When opened with O_RDWR, libfec rewrites corrupted blocks when they are read
    fec::io fh(filename->data, O_RDWR);

    if (!fh) {
        ErrorAbort(state, kLibfecFailure, "fec_open \"%s\" failed: %s", filename->data,
                   strerror(errno));
        return StringValue(strdup(""));
    }

    if (!fh.has_ecc() || !fh.has_verity()) {
        ErrorAbort(state, kLibfecFailure, "unable to use metadata to correct errors");
        return StringValue(strdup(""));
    }

    fec_status status;

    if (!fh.get_status(status)) {
        ErrorAbort(state, kLibfecFailure, "failed to read FEC status");
        return StringValue(strdup(""));
    }

    RangeSet rs;
    parse_range(ranges->data, rs);

    uint8_t buffer[BLOCKSIZE];

    for (size_t i = 0; i < rs.count; ++i) {
        for (size_t j = rs.pos[i * 2]; j < rs.pos[i * 2 + 1]; ++j) {
            // Stay within the data area, libfec validates and corrects metadata
            if (status.data_size <= (uint64_t)j * BLOCKSIZE) {
                continue;
            }

            if (fh.pread(buffer, BLOCKSIZE, (off64_t)j * BLOCKSIZE) != BLOCKSIZE) {
                ErrorAbort(state, kLibfecFailure, "failed to recover %s (block %zu): %s",
                           filename->data, j, strerror(errno));
                return StringValue(strdup(""));
            }

            // If we want to be able to recover from a situation where rewriting a corrected
            // block doesn't guarantee the same data will be returned when re-read later, we
            // can save a copy of corrected blocks to /cache. Note:
            //
            //  1. Maximum space required from /cache is the same as the maximum number of
            //     corrupted blocks we can correct. For RS(255, 253) and a 2 GiB partition,
            //     this would be ~16 MiB, for example.
            //
            //  2. To find out if this block was corrupted, call fec_get_status after each
            //     read and check if the errors field value has increased.
        }
    }
    fprintf(stderr, "...%s image recovered successfully.\n", filename->data);
    return StringValue(strdup("t"));
}

void RegisterBlockImageFunctions() {
    RegisterFunction("block_image_verify", BlockImageVerifyFn);
    RegisterFunction("block_image_update", BlockImageUpdateFn);
    RegisterFunction("block_image_recover", BlockImageRecoverFn);
    RegisterFunction("check_first_block", CheckFirstBlockFn);
    RegisterFunction("range_sha1", RangeSha1Fn);
}
