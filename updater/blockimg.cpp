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

#include <functional>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include <android-base/logging.h>
#include <android-base/parseint.h>
#include <android-base/strings.h>
#include <android-base/unique_fd.h>
#include <applypatch/applypatch.h>
#include <openssl/sha.h>
#include <private/android_filesystem_config.h>
#include <ziparchive/zip_archive.h>

#include "edify/expr.h"
#include "error_code.h"
#include "updater/install.h"
#include "ota_io.h"
#include "print_sha1.h"
#include "updater/updater.h"

// Set this to 0 to interpret 'erase' transfers to mean do a
// BLKDISCARD ioctl (the normal behavior).  Set to 1 to interpret
// erase to mean fill the region with zeroes.
#define DEBUG_ERASE  0

static constexpr size_t BLOCKSIZE = 4096;
static constexpr const char* STASH_DIRECTORY_BASE = "/cache/recovery";
static constexpr mode_t STASH_DIRECTORY_MODE = 0700;
static constexpr mode_t STASH_FILE_MODE = 0600;

struct RangeSet {
  size_t count;  // Limit is INT_MAX.
  size_t size;
  std::vector<size_t> pos;  // Actual limit is INT_MAX.

  // Get the block number for the ith(starting from 0) block in the range set.
  int get_block(size_t idx) const {
    if (idx >= size) {
      LOG(ERROR) << "index: " << idx << " is greater than range set size: " << size;
      return -1;
    }
    for (size_t i = 0; i < pos.size(); i += 2) {
      if (idx < pos[i + 1] - pos[i]) {
        return pos[i] + idx;
      }
      idx -= (pos[i + 1] - pos[i]);
    }
    return -1;
  }
};

static CauseCode failure_type = kNoCause;
static bool is_retry = false;
static std::unordered_map<std::string, RangeSet> stash_map;

static RangeSet parse_range(const std::string& range_text) {
  RangeSet rs;

  std::vector<std::string> pieces = android::base::Split(range_text, ",");
  if (pieces.size() < 3) {
    goto err;
  }

  size_t num;
  if (!android::base::ParseUint(pieces[0], &num, static_cast<size_t>(INT_MAX))) {
    goto err;
  }

  if (num == 0 || num % 2) {
    goto err;  // must be even
  } else if (num != pieces.size() - 1) {
    goto err;
  }

  rs.pos.resize(num);
  rs.count = num / 2;
  rs.size = 0;

  for (size_t i = 0; i < num; i += 2) {
    if (!android::base::ParseUint(pieces[i + 1], &rs.pos[i], static_cast<size_t>(INT_MAX))) {
      goto err;
    }

    if (!android::base::ParseUint(pieces[i + 2], &rs.pos[i + 1], static_cast<size_t>(INT_MAX))) {
      goto err;
    }

    if (rs.pos[i] >= rs.pos[i + 1]) {
      goto err;  // empty or negative range
    }

    size_t sz = rs.pos[i + 1] - rs.pos[i];
    if (rs.size > SIZE_MAX - sz) {
      goto err;  // overflow
    }

    rs.size += sz;
  }

  return rs;

err:
  LOG(ERROR) << "failed to parse range '" << range_text << "'";
  exit(EXIT_FAILURE);
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
            PLOG(ERROR) << "read failed";
            return -1;
        } else if (r == 0) {
            failure_type = kFreadFailure;
            LOG(ERROR) << "read reached unexpected EOF.";
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
            PLOG(ERROR) << "write failed";
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
        PLOG(ERROR) << "BLKDISCARD ioctl failed";
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
        PLOG(ERROR) << "lseek64 failed";
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
    // 如果buffer_alloc >= size, 说明buffer指向的内存>=size,就没必须继续申请,可以重用buffer
    if (size <= buffer.size()) return;

    buffer.resize(size);
}

// 在RangeSinkWrite中实现将system.new.data解压后的数据写入target的功能
// RangeSinkWrite 相对于函数FileSink和MemorySink,是将一个区间段数据写入闪存
// 1 在BlockImageUpdateFn中执行transfer.list中的imgdiff或bsdiff命令时,调用ApplyImagePatch或ApplyBSDiffPatch时传入的sink函数指针
// 2 receive_new_data中直接调用
// data -- 要写入的数据的起始地址
// size -- 要写入的数据大小
// token -- 
struct RangeSinkState {
    explicit RangeSinkState(RangeSet& rs) : tgt(rs) { };

    int fd;
    const RangeSet& tgt;
    size_t p_block;
    size_t p_remain;
};

static ssize_t RangeSinkWrite(const uint8_t* data, ssize_t size, void* token) {
    RangeSinkState* rss = reinterpret_cast<RangeSinkState*>(token);

    if (rss->p_remain == 0) {
        LOG(ERROR) << "range sink write overrun";
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
            ++rss->p_block;
            if (rss->p_block < rss->tgt.count) {
                // 对于BlockImageUpdateFn中的调用,		RangeSinkState rss; current_range_left_  = (tgt->pos[1] - tgt->pos[0]) * BLOCKSIZE;
                // RangeSinkState的p_remain代表剩余要从内存写入闪存的数据大小
                rss->p_remain = (rss->tgt.pos[rss->p_block * 2 + 1] -
                                 rss->tgt.pos[rss->p_block * 2]) * BLOCKSIZE;

                off64_t offset = static_cast<off64_t>(rss->tgt.pos[rss->p_block*2]) * BLOCKSIZE;
                if (!discard_blocks(rss->fd, offset, rss->p_remain)) {
                    break;
                }

                if (!check_lseek(rss->fd, offset, SEEK_SET)) {
                    break;
                }

            } else {
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

struct NewThreadInfo {
    ZipArchiveHandle za;
    ZipEntry entry;

    RangeSinkState* rss;

    pthread_mutex_t mu;
    pthread_cond_t cv;
};

// 相关调用顺序为:BlockImageUpdateFn--unzip_new_data--mzProcessZipEntryContents--processDeflatedEntry或processStoredEntry--receive_new_data
static bool receive_new_data(const uint8_t* data, size_t size, void* cookie) {
    NewThreadInfo* nti = reinterpret_cast<NewThreadInfo*>(cookie);

    while (size > 0) {
        // Wait for nti->rss to be non-null, indicating some of this
        // data is wanted.
        // nti->rss在BlockImageUpdateFn开始为NULL,
        //			pthread_mutex_lock(&nti.mu);
        //			nti.rss = &rss; 					 在解析system.transfer.list循环中如果遇见new命令,主线程就会在互斥锁中给nti->rss赋值
        //			pthread_cond_broadcast(&nti.cv);
        //			while (nti.rss) {  //在receive_new_data函数中在所有解压system.new.data的数据都写入完后将nti->rss=NULL, 在这之前主线程BlockImageUpdateFn一直阻塞
        //				pthread_cond_wait(&nti.cv, &nti.mu); 
        //			}
        //			pthread_mutex_unlock(&nti.mu);
        // nti的mu,cv都是线程相关的信号量, pthread_mutex_t mu;  pthread_cond_t cv; 
        pthread_mutex_lock(&nti->mu);
        //receive_new_data所在的后台线程执行到这里就一直等待主线程执行nti.rss = &rss;
        while (nti->rss == nullptr) {
            pthread_cond_wait(&nti->cv, &nti->mu);
        }
        pthread_mutex_unlock(&nti->mu);

        // while跳出后说明主线程执行了nti.rss = &rss;  其中RangeSinkState rss;	rss.fd = fd;  rss.tgt = tgt;   rss.p_block = 0;  rss.p_remain = (tgt->pos[1] - tgt->pos[0]) * BLOCKSIZE;
        // At this point nti->rss is set, and we own it.  The main
        // thread is waiting for it to disappear from nti.
        ssize_t written = RangeSinkWrite(data, size, nti->rss);
        // RangeSinkWrite返回写入数据多少,因此写入地址data要加上返回值written,要写入多少size要减返回值
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
    NewThreadInfo* nti = static_cast<NewThreadInfo*>(cookie);
    // unzip_new_data函数主要调用mzProcessZipEntryContents完成对system.new.data文件的解压
    ProcessZipEntryContents(nti->za, &nti->entry, receive_new_data, nti);
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
    // 在这个for中把src rangeset表示的所有block区间的数据读到buffer指向的内存中
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
    android::base::unique_fd fd;
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

// Print the hash in hex for corrupted source blocks (excluding the stashed blocks which is
// handled separately).
static void PrintHashForCorruptedSourceBlocks(const CommandParameters& params,
                                              const std::vector<uint8_t>& buffer) {
  LOG(INFO) << "unexpected contents of source blocks in cmd:\n" << params.cmdline;
  CHECK(params.tokens[0] == "move" || params.tokens[0] == "bsdiff" ||
        params.tokens[0] == "imgdiff");

  size_t pos = 0;
  // Command example:
  // move <onehash> <tgt_range> <src_blk_count> <src_range> [<loc_range> <stashed_blocks>]
  // bsdiff <offset> <len> <src_hash> <tgt_hash> <tgt_range> <src_blk_count> <src_range>
  //        [<loc_range> <stashed_blocks>]
  if (params.tokens[0] == "move") {
    // src_range for move starts at the 4th position.
    if (params.tokens.size() < 5) {
      LOG(ERROR) << "failed to parse source range in cmd:\n" << params.cmdline;
      return;
    }
    pos = 4;
  } else {
    // src_range for diff starts at the 7th position.
    if (params.tokens.size() < 8) {
      LOG(ERROR) << "failed to parse source range in cmd:\n" << params.cmdline;
      return;
    }
    pos = 7;
  }

  // Source blocks in stash only, no work to do.
  if (params.tokens[pos] == "-") {
    return;
  }

  RangeSet src = parse_range(params.tokens[pos++]);

  RangeSet locs;
  // If there's no stashed blocks, content in the buffer is consecutive and has the same
  // order as the source blocks.
  if (pos == params.tokens.size()) {
    locs.count = 1;
    locs.size = src.size;
    locs.pos = { 0, src.size };
  } else {
    // Otherwise, the next token is the offset of the source blocks in the target range.
    // Example: for the tokens <4,63946,63947,63948,63979> <4,6,7,8,39> <stashed_blocks>;
    // We want to print SHA-1 for the data in buffer[6], buffer[8], buffer[9] ... buffer[38];
    // this corresponds to the 32 src blocks #63946, #63948, #63949 ... #63978.
    locs = parse_range(params.tokens[pos++]);
    CHECK_EQ(src.size, locs.size);
    CHECK_EQ(locs.pos.size() % 2, static_cast<size_t>(0));
  }

  LOG(INFO) << "printing hash in hex for " << src.size << " source blocks";
  for (size_t i = 0; i < src.size; i++) {
    int block_num = src.get_block(i);
    CHECK_NE(block_num, -1);
    int buffer_index = locs.get_block(i);
    CHECK_NE(buffer_index, -1);
    CHECK_LE((buffer_index + 1) * BLOCKSIZE, buffer.size());

    uint8_t digest[SHA_DIGEST_LENGTH];
    SHA1(buffer.data() + buffer_index * BLOCKSIZE, BLOCKSIZE, digest);
    std::string hexdigest = print_sha1(digest);
    LOG(INFO) << "  block number: " << block_num << ", SHA-1: " << hexdigest;
  }
}

// If the calculated hash for the whole stash doesn't match the stash id, print the SHA-1
// in hex for each block.
static void PrintHashForCorruptedStashedBlocks(const std::string& id,
                                               const std::vector<uint8_t>& buffer,
                                               const RangeSet& src) {
  LOG(INFO) << "printing hash in hex for stash_id: " << id;
  CHECK_EQ(src.size * BLOCKSIZE, buffer.size());

  for (size_t i = 0; i < src.size; i++) {
    int block_num = src.get_block(i);
    CHECK_NE(block_num, -1);

    uint8_t digest[SHA_DIGEST_LENGTH];
    SHA1(buffer.data() + i * BLOCKSIZE, BLOCKSIZE, digest);
    std::string hexdigest = print_sha1(digest);
    LOG(INFO) << "  block number: " << block_num << ", SHA-1: " << hexdigest;
  }
}

// If the stash file doesn't exist, read the source blocks this stash contains and print the
// SHA-1 for these blocks.
static void PrintHashForMissingStashedBlocks(const std::string& id, int fd) {
  if (stash_map.find(id) == stash_map.end()) {
    LOG(ERROR) << "No stash saved for id: " << id;
    return;
  }

  LOG(INFO) << "print hash in hex for source blocks in missing stash: " << id;
  const RangeSet& src = stash_map[id];
  std::vector<uint8_t> buffer(src.size * BLOCKSIZE);
  if (ReadBlocks(src, buffer, fd) == -1) {
      LOG(ERROR) << "failed to read source blocks for stash: " << id;
      return;
  }
  PrintHashForCorruptedStashedBlocks(id, buffer, src);
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
            LOG(ERROR) << "failed to verify blocks (expected " << expected << ", read "
                       << hexdigest << ")";
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
    fn += "/" + base + "/" + id + postfix;

    return fn;
}

// Does a best effort enumeration of stash files. Ignores possible non-file items in the stash
// directory and continues despite of errors. Calls the 'callback' function for each file.
// enumeration 列举 枚举
// EnumerateStash(dirname, DeletePartial, NULL);
// EnumerateStash(dirname, UpdateFileSize, &size);
// dirname -- /cache/recovery/{base}
// callback -- 函数DeletePartial或者UpdateFileSize
static void EnumerateStash(const std::string& dirname,
                           const std::function<void(const std::string&)>& callback) {
  if (dirname.empty()) return;

  //调用opendir, 因为dirname指向的是一个文件夹
  std::unique_ptr<DIR, decltype(&closedir)> directory(opendir(dirname.c_str()), closedir);

  if (directory == nullptr) {
    if (errno != ENOENT) {
      PLOG(ERROR) << "opendir \"" << dirname << "\" failed";
    }
    return;
  }

  dirent* item;
  //循环处理dirname文件夹下的所有文件和文件夹
  while ((item = readdir(directory.get())) != nullptr) {
    //对于不是常规文件的所有情况都直接跳过 DT_REG        This is a regular file.
    if (item->d_type != DT_REG) continue;
    //在PerformBlockImageUpdate中先调用DeletePartial,再调用UpdateFileSize
    // dirname + "/" + item->d_name指向字符串 "/cache/recovery/{base}/{常规文件的文件名}"
    callback(dirname + "/" + item->d_name);
  }
}

// Deletes the stash directory and all files in it. Assumes that it only
// contains files. There is nothing we can do about unlikely, but possible
// errors, so they are merely logged.
static void DeleteFile(const std::string& fn) {
  if (fn.empty()) return;

  LOG(INFO) << "deleting " << fn;

  if (unlink(fn.c_str()) == -1 && errno != ENOENT) {
    PLOG(ERROR) << "unlink \"" << fn << "\" failed";
  }
}

static void DeleteStash(const std::string& base) {
  if (base.empty()) return;

  LOG(INFO) << "deleting stash " << base;

  std::string dirname = GetStashFileName(base, "", "");
  EnumerateStash(dirname, DeleteFile);

  if (rmdir(dirname.c_str()) == -1) {
    if (errno != ENOENT && errno != ENOTDIR) {
      PLOG(ERROR) << "rmdir \"" << dirname << "\" failed";
    }
  }
}

static int LoadStash(CommandParameters& params, const std::string& id, bool verify, size_t* blocks,
                     std::vector<uint8_t>& buffer, bool printnoent) {
    // In verify mode, if source range_set was saved for the given hash,
    // check contents in the source blocks first. If the check fails,
    // search for the stashed files on /cache as usual.
    if (!params.canwrite) {
        if (stash_map.find(id) != stash_map.end()) {
            const RangeSet& src = stash_map[id];
            allocate(src.size * BLOCKSIZE, buffer);

            if (ReadBlocks(src, buffer, params.fd) == -1) {
                LOG(ERROR) << "failed to read source blocks in stash map.";
                return -1;
            }
            if (VerifyBlocks(id, buffer, src.size, true) != 0) {
                LOG(ERROR) << "failed to verify loaded source blocks in stash map.";
                PrintHashForCorruptedStashedBlocks(id, buffer, src);
                return -1;
            }
            return 0;
        }
    }

    size_t blockcount = 0;

    if (!blocks) {
        blocks = &blockcount;
    }

    std::string fn = GetStashFileName(params.stashbase, id, "");

    struct stat sb;
    int res = stat(fn.c_str(), &sb);

    if (res == -1) {
        if (errno != ENOENT || printnoent) {
            PLOG(ERROR) << "stat \"" << fn << "\" failed";
            PrintHashForMissingStashedBlocks(id, params.fd);
        }
        return -1;
    }

    LOG(INFO) << " loading " << fn;

    if ((sb.st_size % BLOCKSIZE) != 0) {
        LOG(ERROR) << fn << " size " << sb.st_size << " not multiple of block size " << BLOCKSIZE;
        return -1;
    }

    android::base::unique_fd fd(TEMP_FAILURE_RETRY(ota_open(fn.c_str(), O_RDONLY)));
    if (fd == -1) {
        PLOG(ERROR) << "open \"" << fn << "\" failed";
        return -1;
    }

    allocate(sb.st_size, buffer);

    if (read_all(fd, buffer, sb.st_size) == -1) {
        return -1;
    }

    *blocks = sb.st_size / BLOCKSIZE;

    if (verify && VerifyBlocks(id, buffer, *blocks, true) != 0) {
        LOG(ERROR) << "unexpected contents in " << fn;
        if (stash_map.find(id) == stash_map.end()) {
            LOG(ERROR) << "failed to find source blocks number for stash " << id
                       << " when executing command: " << params.cmdname;
        } else {
            const RangeSet& src = stash_map[id];
            PrintHashForCorruptedStashedBlocks(id, buffer, src);
        }
        DeleteFile(fn);
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
        LOG(ERROR) << "not enough space to write stash";
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
            LOG(INFO) << " skipping " << blocks << " existing blocks in " << cn;
            *exists = true;
            return 0;
        }

        *exists = false;
    }

    LOG(INFO) << " writing " << blocks << " blocks to " << cn;

    android::base::unique_fd fd(
        TEMP_FAILURE_RETRY(ota_open(fn.c_str(), O_WRONLY | O_CREAT | O_TRUNC, STASH_FILE_MODE)));
    if (fd == -1) {
        PLOG(ERROR) << "failed to create \"" << fn << "\"";
        return -1;
    }

    if (fchown(fd, AID_SYSTEM, AID_SYSTEM) != 0) {  // system user
        PLOG(ERROR) << "failed to chown \"" << fn << "\"";
        return -1;
    }

    if (write_all(fd, buffer, blocks * BLOCKSIZE) == -1) {
        return -1;
    }

    if (ota_fsync(fd) == -1) {
        failure_type = kFsyncFailure;
        PLOG(ERROR) << "fsync \"" << fn << "\" failed";
        return -1;
    }

    if (rename(fn.c_str(), cn.c_str()) == -1) {
        PLOG(ERROR) << "rename(\"" << fn << "\", \"" << cn << "\") failed";
        return -1;
    }

    std::string dname = GetStashFileName(base, "", "");
    android::base::unique_fd dfd(TEMP_FAILURE_RETRY(ota_open(dname.c_str(),
                                                             O_RDONLY | O_DIRECTORY)));
    if (dfd == -1) {
        failure_type = kFileOpenFailure;
        PLOG(ERROR) << "failed to open \"" << dname << "\" failed";
        return -1;
    }

    if (ota_fsync(dfd) == -1) {
        failure_type = kFsyncFailure;
        PLOG(ERROR) << "fsync \"" << dname << "\" failed";
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
static int CreateStash(State* state, size_t maxblocks, const std::string& blockdev,
                       std::string& base) {
  if (blockdev.empty()) {
    return -1;
  }

  // Stash directory should be different for each partition to avoid conflicts
  // when updating multiple partitions at the same time, so we use the hash of
  // the block device name as the base directory
  uint8_t digest[SHA_DIGEST_LENGTH];
  SHA1(reinterpret_cast<const uint8_t*>(blockdev.data()), blockdev.size(), digest);
  // *base指向的就是/dev/block/bootdevice/by-name/system 的40位sha加密 字符串
  // /dev/block/bootdevice/by-name/system -- 2bdde8504898ccfcd2c59f20bb8c9c25f73bb524
  // "/dev/block/bootdevice/by-name/system" -- b00e5a7238619b2074783d82ba78f2c93f2653f9
  base = print_sha1(digest);

  // dirname 指向字符串 "/cache/recovery/{base}"
  std::string dirname = GetStashFileName(base, "", "");
  struct stat sb;
  //stat成功返回0,失败返回-1
  int res = stat(dirname.c_str(), &sb);
  size_t max_stash_size = maxblocks * BLOCKSIZE;

  // if else的两个分支都处理的是stat失败的情况
  if (res == -1 && errno != ENOENT) {
    // 获取/cache/recovery/{base}属性失败, 但失败原因不是因为/cache/recovery/{base}不存在(ENOENT)
    ErrorAbort(state, kStashCreationFailure, "stat \"%s\" failed: %s\n", dirname.c_str(),
               strerror(errno));
    return -1;
  } else if (res != 0) {
    // 说明stat还是不成功,但失败原因就是/cache/recovery/{base}/文件夹不存在,这种情况下可以自行创建/cache/recovery/{base}
    LOG(INFO) << "creating stash " << dirname;
    // mkdir!!! 创建出的/cache/recovery/{base}/是个文件夹,STASH_DIRECTORY_MODE 0700
    res = mkdir(dirname.c_str(), STASH_DIRECTORY_MODE);

    if (res != 0) {
      ErrorAbort(state, kStashCreationFailure, "mkdir \"%s\" failed: %s\n", dirname.c_str(),
                 strerror(errno));
      return -1;
    }

    if (chown(dirname.c_str(), AID_SYSTEM, AID_SYSTEM) != 0) {  // system user
      ErrorAbort(state, kStashCreationFailure, "chown \"%s\" failed: %s\n", dirname.c_str(),
                 strerror(errno));
      return -1;
    }

    // 在cahce分区分配 maxblocks * BLOCKSIZE 字节大小的空间
    if (CacheSizeCheck(max_stash_size) != 0) {
      ErrorAbort(state, kStashCreationFailure, "not enough space for stash (%zu needed)\n",
                 max_stash_size);
      return -1;
    }

    return 1;  // Created directory
  }

  LOG(INFO) << "using existing stash " << dirname;

  // If the directory already exists, calculate the space already allocated to stash files and check
  // if there's enough for all required blocks. Delete any partially completed stash files first.
  // 如果dirname(/cache/recovery/{base})文件夹已经存在的情况
  // 在DeletePartial中删除/cache/recovery/{base}/下所有文件名中含".partial"的普通文件
  EnumerateStash(dirname, [](const std::string& fn) {
    if (android::base::EndsWith(fn, ".partial")) {
      DeleteFile(fn);
    }
  });

  size_t existing = 0;
  //在UpdateFileSize中计算/cache/recovery/{base}/下所有剩余文件的大小总和(以字节为单位),传给size
  EnumerateStash(dirname, [&existing](const std::string& fn) {
    if (fn.empty()) return;
    struct stat sb;
    if (stat(fn.c_str(), &sb) == -1) {
      PLOG(ERROR) << "stat \"" << fn << "\" failed";
      return;
    }
    existing += static_cast<size_t>(sb.st_size);
  });

  if (max_stash_size > existing) {
    // 计算出cache分区还需要分配的空间大小
    size_t needed = max_stash_size - existing;
    // 如果cache分区分配 还需要分配的空间大小 失败
    if (CacheSizeCheck(needed) != 0) {
      ErrorAbort(state, kStashCreationFailure, "not enough space for stash (%zu more needed)\n",
                 needed);
      return -1;
    }
  }

  return 0;  // Using existing directory
}

// FreeStash中将会直接删除/cache/recovery/{hash值} 下暂存的文件
static int FreeStash(const std::string& base, const std::string& id) {
  if (base.empty() || id.empty()) {
    return -1;
  }

  DeleteFile(GetStashFileName(base, id, ""));

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
// On return, params.buffer is filled with the loaded source data (rearranged and combined with
// stashed data as necessary). buffer may be reallocated if needed to accommodate the source data.
// *tgt is the target RangeSet. Any stashes required are loaded using LoadStash.

static int LoadSrcTgtVersion2(CommandParameters& params, RangeSet& tgt, size_t& src_blocks,
                              bool* overlap) {

    // At least it needs to provide three parameters: <tgt_range>,
    // <src_block_count> and "-"/<src_range>.
    if (params.cpos + 2 >= params.tokens.size()) {
        LOG(ERROR) << "invalid parameters";
        return -1;
    }

    // <tgt_range>
    tgt = parse_range(params.tokens[params.cpos++]);

    // <src_block_count>
    const std::string& token = params.tokens[params.cpos++];
    if (!android::base::ParseUint(token.c_str(), &src_blocks)) {
        LOG(ERROR) << "invalid src_block_count \"" << token << "\"";
        return -1;
    }

    allocate(src_blocks * BLOCKSIZE, params.buffer);

    // "-" or <src_range> [<src_loc>]
    if (params.tokens[params.cpos] == "-") {
        // no source ranges, only stashes
        params.cpos++;
    } else {
        RangeSet src = parse_range(params.tokens[params.cpos++]);
        int res = ReadBlocks(src, params.buffer, params.fd);

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

        RangeSet locs = parse_range(params.tokens[params.cpos++]);
        MoveRange(params.buffer, locs, params.buffer);
    }

    // <[stash_id:stash_range]>
    while (params.cpos < params.tokens.size()) {
        // Each word is a an index into the stash table, a colon, and
        // then a rangeset describing where in the source block that
        // stashed data should go.
        std::vector<std::string> tokens = android::base::Split(params.tokens[params.cpos++], ":");
        if (tokens.size() != 2) {
            LOG(ERROR) << "invalid parameter";
            return -1;
        }

        std::vector<uint8_t> stash;
        int res = LoadStash(params, tokens[0], false, nullptr, stash, true);

        if (res == -1) {
            // These source blocks will fail verification if used later, but we
            // will let the caller decide if this is a fatal failure
            LOG(ERROR) << "failed to load stash " << tokens[0];
            continue;
        }

        RangeSet locs = parse_range(tokens[1]);

        MoveRange(params.buffer, locs, stash);
    }

    return 0;
}

/**
 * Do a source/target load for move/bsdiff/imgdiff in version 3.
 *
 * We expect to parse the remainder of the parameter tokens as one of:
 *
 *    <tgt_range> <src_block_count> <src_range>
 *        (loads data from source image only)
 *
 *    <tgt_range> <src_block_count> - <[stash_id:stash_range] ...>
 *        (loads data from stashes only)
 *
 *    <tgt_range> <src_block_count> <src_range> <src_loc> <[stash_id:stash_range] ...>
 *        (loads data from both source image and stashes)
 *
 * Parameters are the same as for LoadSrcTgtVersion2, except for 'onehash', which tells the function
 * whether to expect separate source and targe block hashes, or if they are both the same and only
 * one hash should be expected, and 'isunresumable', which receives a non-zero value if block
 * verification fails in a way that the update cannot be resumed anymore.
 *
 * If the function is unable to load the necessary blocks or their contents don't match the hashes,
 * the return value is -1 and the command should be aborted.
 *
 * If the return value is 1, the command has already been completed according to the contents of the
 * target blocks, and should not be performed again.
 *
 * If the return value is 0, source blocks have expected content and the command can be performed.
 */
 // PerformCommandMove和PerformCommandDiff中调用LoadSrcTgtVersion3时overlap都为0.
static int LoadSrcTgtVersion3(CommandParameters& params, RangeSet& tgt, size_t& src_blocks,
                              bool onehash, bool& overlap) {
    if (params.cpos >= params.tokens.size()) {
        LOG(ERROR) << "missing source hash";
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
            LOG(ERROR) << "missing target hash";
            return -1;
        }
        tgthash = params.tokens[params.cpos++];
    }

    if (LoadSrcTgtVersion2(params, tgt, src_blocks, &overlap) == -1) {
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
        // Target blocks already have expected content, command should be skipped.
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
            LOG(INFO) << "stashing " << src_blocks << " overlapping blocks to " << srchash;

            bool stash_exists = false;
            if (WriteStash(params.stashbase, srchash, src_blocks, params.buffer, true,
                           &stash_exists) != 0) {
                LOG(ERROR) << "failed to stash overlapping source blocks";
                return -1;
            }

            params.stashed += src_blocks;
            // Can be deleted when the write has completed.
            if (!stash_exists) {
                // 在WriteStash写入成功后可以将srchash保存到params->freestash中
                params.freestash = srchash;
            }
        }

        // 不管有没有重叠,这种情况都说明Source blocks have expected content, 到这里就可以跳到函数最后并返回0
        // 函数返回0代表source blocks与期待的匹配,命令可以执行
        // 正常升级没有任何中断重启的情况下,第一次执行的命令都是走到这里
        // Source blocks have expected content, command can proceed.
        return 0;
    }

	// 执行到这里说明从block_image_verify第一个参数读取到的target与tgt hash不匹配, 同时从source或(和)stash中读取的数据(params->buffer)与src hash也不匹配
	// 这种情况下, 如果source blocks和target blocks有重叠,重叠的source blocks在之前会被暂存, 这时就可以调用LoadStash把之前暂停的stash文件(/cache/recovery/{stashbase}/{srchash})读取到params->buffer中.
	// 如果执行transfer.list中的命令时突然手机重启,重启后恢复更新就会走到这一步, 这种情况下无法判断stash是否可以删除
    if (overlap && LoadStash(params, srchash, true, nullptr, params.buffer, true) == 0) {
        // 如果LoadStash读取成功,到这里就可以跳到函数最后并返回0
        // Overlapping source blocks were previously stashed, command can proceed.
        // We are recovering from an interrupted command, so we don't know if the
        // stash can safely be deleted after this command.
        // 这种情况仍然可以认为src加载成功,source blocks与期待的匹配,命令可以执行
        return 0;
    }

	// 这种情况下, 如果source blocks和target blocks没有重叠,或者上面的LoadStash读取失败
    // 说明确实遇到了与期望不匹配的数据,更新不能继续,这时将params->isunresumable标记为1,函数返回-1表示失败
    // Valid source data not available, update cannot be resumed.
    LOG(ERROR) << "partition has unexpected contents";
    PrintHashForCorruptedSourceBlocks(params, params.buffer);

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
  RangeSet tgt;
  // 执行LoadSrcTgtVersion1或LoadSrcTgtVersion2后,tgt就会保存target的block range信息
  //对于LoadSrcTgtVersion1,LoadSrcTgtVersion2,LoadSrcTgtVersion3, 这三个函数总体上都是将src或stash中的内容复制到内存中开辟的一段buffer中(params->buffer)
  //都不涉及之后的写入操作, 写入操作在之后根据params->canwrite来选择执行. 对于block_image_verify, params->canwrite为0,因此block_image_verify在执行move时就不会写入
  int status = LoadSrcTgtVersion3(params, tgt, blocks, true, overlap);

  if (status == -1) {
    LOG(ERROR) << "failed to read blocks for move";
    return -1;
  }

  if (status == 0) {
    params.foundwrites = true;
  } else if (params.foundwrites) {
    LOG(WARNING) << "warning: commands executed out of order [" << params.cmdname << "]";
  }

  if (params.canwrite) {
    if (status == 0) {
      LOG(INFO) << "  moving " << blocks << " blocks";

      //从blockdev_filename->data中取偏移,将buffer中的内容写入blockdev_filename->data
      if (WriteBlocks(tgt, params.buffer, params.fd) == -1) {
        return -1;
      }
    } else {
      LOG(INFO) << "skipping " << blocks << " already moved blocks";
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
  // <stash_id> <src_range>
  if (params.cpos + 1 >= params.tokens.size()) {
    LOG(ERROR) << "missing id and/or src range fields in stash command";
    return -1;
  }

  const std::string& id = params.tokens[params.cpos++];
  size_t blocks = 0;
  if (LoadStash(params, id, true, &blocks, params.buffer, false) == 0) {
    // Stash file already exists and has expected contents. Do not read from source again, as the
    // source may have been already overwritten during a previous attempt.
    return 0;
  }

  RangeSet src = parse_range(params.tokens[params.cpos++]);

  allocate(src.size * BLOCKSIZE, params.buffer);
  if (ReadBlocks(src, params.buffer, params.fd) == -1) {
    return -1;
  }
  blocks = src.size;
  stash_map[id] = src;

  if (VerifyBlocks(id, params.buffer, blocks, true) != 0) {
    // Source blocks have unexpected contents. If we actually need this data later, this is an
    // unrecoverable error. However, the command that uses the data may have already completed
    // previously, so the possible failure will occur during source block verification.
    LOG(ERROR) << "failed to load source blocks for stash " << id;
    return 0;
  }

  // In verify mode, we don't need to stash any blocks.
  if (!params.canwrite) {
    return 0;
  }

  LOG(INFO) << "stashing " << blocks << " blocks to " << id;
  params.stashed += blocks;
  return WriteStash(params.stashbase, id, blocks, params.buffer, false, nullptr);
}

static int PerformCommandFree(CommandParameters& params) {
  // <stash_id>
  if (params.cpos >= params.tokens.size()) {
    LOG(ERROR) << "missing stash id in free command";
    return -1;
  }

  const std::string& id = params.tokens[params.cpos++];
  stash_map.erase(id);

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
        LOG(ERROR) << "missing target blocks for zero";
        return -1;
    }

    // 将word所有信息解析,保存到tgt结构体中.
    RangeSet tgt = parse_range(params.tokens[params.cpos++]);

    // tgt->size = 30个block编号组成的15个范围的 (右边-左边) 之和
    LOG(INFO) << "  zeroing " << tgt.size << " blocks";

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
        LOG(ERROR) << "missing target blocks for new";
        return -1;
    }

    // tgt保存30后所有信息
    RangeSet tgt = parse_range(params.tokens[params.cpos++]);

    if (params.canwrite) {
        LOG(INFO) << " writing " << tgt.size << " blocks of new data";

        RangeSinkState rss(tgt);
        rss.fd = params.fd;
        rss.p_block = 0;
        rss.p_remain = (tgt.pos[1] - tgt.pos[0]) * BLOCKSIZE;

        off64_t offset = static_cast<off64_t>(tgt.pos[0]) * BLOCKSIZE;
        if (!discard_blocks(params.fd, offset, tgt.size * BLOCKSIZE)) {
            return -1;
        }

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
        LOG(ERROR) << "missing patch offset or length for " << params.cmdname;
        return -1;
    }

    size_t offset;
    // 解析得到bsdiff/imgdiff命令的  patch offset参数
    if (!android::base::ParseUint(params.tokens[params.cpos++].c_str(), &offset)) {
        LOG(ERROR) << "invalid patch offset";
        return -1;
    }

    size_t len;
    // 解析得到bsdiff/imgdiff命令的  patch length参数
    if (!android::base::ParseUint(params.tokens[params.cpos++].c_str(), &len)) {
        LOG(ERROR) << "invalid patch len";
        return -1;
    }

    RangeSet tgt;
    size_t blocks = 0;
    bool overlap = false;
    int status = LoadSrcTgtVersion3(params, tgt, blocks, false, overlap);

    if (status == -1) {
        LOG(ERROR) << "failed to read blocks for diff";
        return -1;
    }

    if (status == 0) {
        params.foundwrites = true;
    } else if (params.foundwrites) {
        LOG(WARNING) << "warning: commands executed out of order [" << params.cmdname << "]";
    }

    if (params.canwrite) {
        if (status == 0) {
            LOG(INFO) << "patching " << blocks << " blocks to " << tgt.size;
            // patch_start是ota压缩包中system.patch.dat文件在内存中的绝对地址, patch_offset是imgdiff或bsdiff命令要打的补丁数据在system.patch.dat中的相对地址
            // 因此patch_value.data指向的就是此补丁数据在system.patch.dat中的绝对地址
            Value patch_value(VAL_BLOB,
                    std::string(reinterpret_cast<const char*>(params.patch_start + offset), len));
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
                    LOG(ERROR) << "Failed to apply image patch.";
                    return -1;
                }
            } else {
                if (ApplyBSDiffPatch(params.buffer.data(), blocks * BLOCKSIZE, &patch_value,
                        0, &RangeSinkWrite, &rss, nullptr) != 0) {
                    LOG(ERROR) << "Failed to apply bsdiff patch.";
                    return -1;
                }
            }

            // We expect the output of the patcher to fill the tgt ranges exactly.
            // 打完pathc后rss.p_block就是新生成的目标大小
            if (rss.p_block != tgt.count || rss.p_remain != 0) {
                //对于ApplyImagePatch或ApplyBSDiffPatch,都是在RangeSinkWrite中完成rss->p_remain-=write_now 正常情况下rss.p_remain应为0
                LOG(ERROR) << "range sink underrun?";
            }
        } else {
            // status为1才能执行到这里,这种情况说明tgt与tgt hash匹配,命令不用执行
            LOG(INFO) << "skipping " << blocks << " blocks already patched to " << tgt.size
                      << " [" << params.cmdline << "]";
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
        PLOG(ERROR) << "failed to fstat device to erase";
        return -1;
    }

    //先根据open(blockdev_filename->data)读到的fd 判断target是不是块设备
    if (!S_ISBLK(sb.st_mode)) {
        LOG(ERROR) << "not a block device; skipping erase";
        return -1;
    }

    if (params.cpos >= params.tokens.size()) {
        LOG(ERROR) << "missing target blocks for erase";
        return -1;
    }

    // range 14,546363,....,753152
    RangeSet tgt = parse_range(params.tokens[params.cpos++]);

    if (params.canwrite) {
        LOG(INFO) << " erasing " << tgt.size << " blocks";

        for (size_t i = 0; i < tgt.count; ++i) {
            uint64_t blocks[2];
            // offset in bytes
            // blocks[0] 每个区间的起始位置
            blocks[0] = tgt.pos[i * 2] * (uint64_t) BLOCKSIZE;
            // length in bytes
            // blocks[1] 每个区间的长度
            blocks[1] = (tgt.pos[i * 2 + 1] - tgt.pos[i * 2]) * (uint64_t) BLOCKSIZE;

            // 调用ioctl屏蔽range描述的块组区间
            if (ioctl(params.fd, BLKDISCARD, &blocks) == -1) {
                PLOG(ERROR) << "BLKDISCARD ioctl failed";
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
static Value* PerformBlockImageUpdate(const char* name, State* state,
                                      const std::vector<std::unique_ptr<Expr>>& argv,
                                      const Command* commands, size_t cmdcount, bool dryrun) {
  CommandParameters params = {};
  params.canwrite = !dryrun;

  LOG(INFO) << "performing " << (dryrun ? "verification" : "update");
  if (state->is_retry) {
    is_retry = true;
    LOG(INFO) << "This update is a retry.";
  }
  if (argv.size() != 4) {
    ErrorAbort(state, kArgsParsingFailure, "block_image_update expects 4 arguments, got %zu",
               argv.size());
    return StringValue("");
  }

  std::vector<std::unique_ptr<Value>> args;
  if (!ReadValueArgs(state, argv, &args)) {
    return nullptr;
  }

  //ReadValueArgs取得脚本中的/dev/block/bootdevice/by-name/system，package_extract_file("system.transfer.list"),system.new.dat", "system.patch.dat"这四个参数，赋值给blockdev_filename ，transfer_list_value， new_data_fn，patch_data_fn
  // 因为block_image_update中有类似package_extract_file("system.transfer.list")这种还需要执行才能得到返回值的函数
  // 在ReadValueArgs中利用va_list等C语言的可变参数宏，将block_image_update的四个输入参数"/dev/block/bootdevice/by-name/system", package_extract_file("system.transfer.list"), "system.new.dat", "system.patch.dat"，分别赋值给blockdev_filename，transfer_list_value，new_data_fn，patch_data_fn
  // ReadValueArgs成功执行后:
  // blockdev_filename -- /dev/block/bootdevice/by-name/system
  // transfer_list_value -- system.transfer.list文件内容
  // new_data_fn -- system.new.dat, new_data_fn -- system.patch.dat
  const Value* blockdev_filename = args[0].get();
  const Value* transfer_list_value = args[1].get();
  const Value* new_data_fn = args[2].get();
  const Value* patch_data_fn = args[3].get();

  if (blockdev_filename->type != VAL_STRING) {
    //在BlockImageUpdateFn函数中name就是block_image_update,这个错误log的意思就是block_image_update的blockdev_filename参数必须是string类型
    ErrorAbort(state, kArgsParsingFailure, "blockdev_filename argument to %s must be string", name);
    return StringValue("");
  }
  // 在package_extract_file("system.transfer.list"),中将type设为了VAL_BLOB
  // BLOB (binary large object)，二进制大对象，是一个可以存储二进制文件的容器 //BLOB是一个大文件，典型的BLOB是一张图片或一个声音文件，由于它们的尺寸，必须使用特殊的方式来处理（例如：上传、下载或者存放到一个数据库）
  if (transfer_list_value->type != VAL_BLOB) {
    ErrorAbort(state, kArgsParsingFailure, "transfer_list argument to %s must be blob", name);
    return StringValue("");
  }
  if (new_data_fn->type != VAL_STRING) {
    ErrorAbort(state, kArgsParsingFailure, "new_data_fn argument to %s must be string", name);
    return StringValue("");
  }
  if (patch_data_fn->type != VAL_STRING) {
    ErrorAbort(state, kArgsParsingFailure, "patch_data_fn argument to %s must be string", name);
    return StringValue("");
  }

  // 这里的ui是updater info的含义，而不是user interface
  // state.cookie = &updater_info;updater_info.cmd_pipe = cmd_pipe; updater_info.package_zip = &za;updater_info.version = atoi(version);updater_info.package_zip_addr = map.addr;
  // updater_info.package_zip_len = map.length;
  UpdaterInfo* ui = static_cast<UpdaterInfo*>(state->cookie);
  if (ui == nullptr) {
    return StringValue("");
  }

  // 升级时updater子进程通过cmd_pipe将progress进度传给recovery进程
  FILE* cmd_pipe = ui->cmd_pipe;
  // za就代表整个zip格式的ota包
  ZipArchiveHandle za = ui->package_zip;

  if (cmd_pipe == nullptr || za == nullptr) {
    return StringValue("");
  }

  ZipString path_data(patch_data_fn->data.c_str());
  //patch_data_fn->data指向的是“system.patch.dat”这段字符串，而不是 system.patch.dat这个文件的内容，
  //因此patch_entry就代表内存中的zip安装包中的system.patch.dat这一项
  // 从ota zip包中找到system.patch.dat文件
  ZipEntry patch_entry;
  if (FindEntry(za, path_data, &patch_entry) != 0) {
    LOG(ERROR) << name << "(): no file \"" << patch_data_fn->data << "\" in package";
    return StringValue("");
  }

  //内存中ota zip包起始地址+system.patch.dat在zip包中的相对偏移,得到system.patch.dat文件在内存中地址
  // 计算出patch_entry的起始地址patch_start，因为注释中说patch stream must be uncompressed
  // patch_start在下面循环中执行bsdiff或imgdiff命令中会用到
  // package_zip_addr + mzGetZipEntryOffset(patch_entry) zip安装包在内存中的绝对地址+ system.patch.dat在zip包内的相对偏移地址
  // 因此patch_start就代表压缩包中system.patch.dat文件在内存中的绝对地址
  params.patch_start = ui->package_zip_addr + patch_entry.offset;
  ZipString new_data(new_data_fn->data.c_str());
  // new_data_fn->data指向字符串"system.new.dat",从ota zip包中找到system.new.dat文件
  //new_data_fn->data指向的数据是“system.new.dat”，而不是system.new.dat这个文件的内容
  //new_entry就代表内存中的zip安装包中的system.new.dat这一项
  ZipEntry new_entry;
  if (FindEntry(za, new_data, &new_entry) != 0) {
    LOG(ERROR) << name << "(): no file \"" << new_data_fn->data << "\" in package";
    return StringValue("");
  }

  // 打开/dev/block/bootdevice/by-name/system等
  params.fd.reset(TEMP_FAILURE_RETRY(ota_open(blockdev_filename->data.c_str(), O_RDWR)));
  if (params.fd == -1) {
    PLOG(ERROR) << "open \"" << blockdev_filename->data << "\" failed";
    return StringValue("");
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

	// pthread_create的四个参数：1指向线程标识符的指针 2 设置线程属性 3 线程运行函数的起始地址 4 运行函数的参数。
	// pthread_create将会创建线程,在线程创建以后，就开始运行相关的线程函数
	// 因此在BlockImageUpdateFn中将会创建出一个线程,
	// 线程标识符--new_data_thread,   //线程属性attr设置为了PTHREAD_CREATE_JOINABLE,代表非分离线程,非分离的线程终止时，其线程ID和退出状态将保留，直到另外一个线程调用pthread_join.
	// 线程函数的起始地址, 这里就是执行unzip_new_data函数
	// nti--传给unzip_new_data函数的参数
	// 创建名为调用unzip_new_data的现场,在其中执行unzip_new_data,在unzip_new_data中调用mzProcessZipEntryContents完成对system.new.data文件的解压
    int error = pthread_create(&params.thread, &attr, unzip_new_data, &params.nti);
    if (error != 0) {
      PLOG(ERROR) << "pthread_create failed";
      return StringValue("");
    }
  }

  std::vector<std::string> lines = android::base::Split(transfer_list_value->data, "\n");
  if (lines.size() < 2) {
    ErrorAbort(state, kArgsParsingFailure, "too few lines in the transfer list [%zd]\n",
               lines.size());
    return StringValue("");
  }

  // First line in transfer list is the version number.
  // line用于保存transfer.list文件的每一单行
  // 读取transfer.list文件的第1行
  if (!android::base::ParseInt(lines[0], &params.version, 3, 4)) {
    // version保存transfer.list文件第一行版本号
    // recovery 5.0 lollipop-erlease对应的api是1
    // d83e4f15890ac6ebe0d61924bd224eb1ae8565ad support for version 2 of block image diffs Change-Id: I4559bfd76d5403859637aeac832f3a5e9e13b63a 开始新增V2
    // commit 90221205a3e58f2a198faa838088dc7bc7c9c752 Support resuming block based OTAs Change-Id: I1e752464134aeb2d396946348e6041acabe13942 开始新增V3
    LOG(ERROR) << "unexpected transfer list version [" << lines[0] << "]";
    return StringValue("");
  }

  LOG(INFO) << "blockimg version is " << params.version;

  // Second line in transfer list is the total number of blocks we expect to write.
  size_t total_blocks;
  // 读取transfer.list文件的第2行
  if (!android::base::ParseUint(lines[1], &total_blocks)) {
    ErrorAbort(state, kArgsParsingFailure, "unexpected block count [%s]\n", lines[1].c_str());
    return StringValue("");
  }

  if (total_blocks == 0) {
    return StringValue("t");
  }

  size_t start = 2;
  if (lines.size() < 4) {
    ErrorAbort(state, kArgsParsingFailure, "too few lines in the transfer list [%zu]\n",
               lines.size());
    return StringValue("");
  }

  // Third line is how many stash entries are needed simultaneously.
  // 对于system.transfer.list文件的第三行,如果版本号>=2,第三行就是同时需要的stash entry
  // transfer.list从V2开始,第3行为同时并存的stash文件数
  LOG(INFO) << "maximum stash entries " << lines[2];

  // Fourth line is the maximum number of blocks that will be stashed simultaneously
  // transfer.list从V2开始,第4行为最大stash文件所占用的block空间数.stash_max_blocks可用于检测是否有足够多可用的内存或零散磁盘空间
  size_t stash_max_blocks;
  if (!android::base::ParseUint(lines[3], &stash_max_blocks)) {
    ErrorAbort(state, kArgsParsingFailure, "unexpected maximum stash blocks [%s]\n",
               lines[3].c_str());
    return StringValue("");
  }

  //stash在 版本号>=2 引入,因此要首先在 /cache/recovery/{base}/文件夹 下创建出足够空间
  int res = CreateStash(state, stash_max_blocks, blockdev_filename->data, params.stashbase);
  if (res == -1) {
    return StringValue("");
  }

  params.createdstash = res;

  start += 2;

  // Build a map of the available commands
  // cmdcount对于BlockImageVerifyFn 和 BlockImageUpdateF都是8,第二个参数也都是NULL
  std::unordered_map<std::string, const Command*> cmd_map;
  for (size_t i = 0; i < cmdcount; ++i) {
    if (cmd_map.find(commands[i].name) != cmd_map.end()) {
      LOG(ERROR) << "Error: command [" << commands[i].name << "] already exists in the cmd map.";
      return StringValue(strdup(""));
    }
    //将Verify或Update支持的命令写入hash表中
    cmd_map[commands[i].name] = &commands[i];
  }

  int rc = -1;

  // Subsequent lines are all individual transfer commands
  // 第四行后面的各行都是独立的命令,在这个for循环中依次读取并执行每行命令
  for (auto it = lines.cbegin() + start; it != lines.cend(); it++) {
    const std::string& line(*it);
    if (line.empty()) continue;

    params.tokens = android::base::Split(line, " ");
    params.cpos = 0;
    // params.cmdname保存每行开头的命令名称
    params.cmdname = params.tokens[params.cpos++].c_str();
    params.cmdline = line.c_str();

    if (cmd_map.find(params.cmdname) == cmd_map.end()) {
      LOG(ERROR) << "unexpected command [" << params.cmdname << "]";
      goto pbiudone;
    }

	// 在Verify或Update保存的hash表中查找这行开头的命令是否支持
    const Command* cmd = cmd_map[params.cmdname];

    // 对于BlockImageVerifyFn,如果传入的commands数组中name对应的操作函数为NULL,则这里cmd->f就为NULL,所以BlockImageVerifyFn在解析system.transfer.list时就会跳过不支持的命令
    // 对于BlockImageVerifyFn和BlockImageUpdateFn支持的命令,cmd->f就不为NULL,因此cmd->f(&params)就是在这个for循环中执行每行支持的命令
    if (cmd->f != nullptr && cmd->f(params) == -1) {
      LOG(ERROR) << "failed to execute command [" << line << "]";
      goto pbiudone;
    }

    if (params.canwrite) {
      // 调用pthread_join等待子线程new_data_thread的结束
      if (ota_fsync(params.fd) == -1) {
        failure_type = kFsyncFailure;
        PLOG(ERROR) << "fsync failed";
        goto pbiudone;
      }
      fprintf(cmd_pipe, "set_progress %.4f\n", static_cast<double>(params.written) / total_blocks);
      fflush(cmd_pipe);
    }
  }

  if (params.canwrite) {
    pthread_join(params.thread, nullptr);

    // blocks_so_far为实际写入的block个数,total_blocks为升级脚本第二行计划写入的block个数.正常情况下两者相等.
    LOG(INFO) << "wrote " << params.written << " blocks; expected " << total_blocks;
    LOG(INFO) << "stashed " << params.stashed << " blocks";
    // 这是buffer_alloc的大小就是执行transfer.list中命令过程中最大分配的一段内存大小
    LOG(INFO) << "max alloc needed was " << params.buffer.size();

    const char* partition = strrchr(blockdev_filename->data.c_str(), '/');
    if (partition != nullptr && *(partition + 1) != 0) {
      fprintf(cmd_pipe, "log bytes_written_%s: %zu\n", partition + 1, params.written * BLOCKSIZE);
      fprintf(cmd_pipe, "log bytes_stashed_%s: %zu\n", partition + 1, params.stashed * BLOCKSIZE);
      fflush(cmd_pipe);
    }
    // Delete stash only after successfully completing the update, as it may contain blocks needed
    // to complete the update later.
    DeleteStash(params.stashbase);
  } else {
    LOG(INFO) << "verified partition contents; update may be resumed";
  }

  rc = 0;

pbiudone:
  if (ota_fsync(params.fd) == -1) {
    failure_type = kFsyncFailure;
    PLOG(ERROR) << "fsync failed";
  }
  // params.fd will be automatically closed because it's a unique_fd.

  // Only delete the stash if the update cannot be resumed, or it's a verification run and we
  // created the stash.
  if (params.isunresumable || (!params.canwrite && params.createdstash)) {
    DeleteStash(params.stashbase);
  }

  if (failure_type != kNoCause && state->cause_code == kNoCause) {
    state->cause_code = failure_type;
  }

  return StringValue(rc == 0 ? "t" : "");
}

/**
 * The transfer list is a text file containing commands to transfer data from one place to another
 * on the target partition. We parse it and execute the commands in order:
 *
 *    zero [rangeset]
 *      - Fill the indicated blocks with zeros.
 *
 *    new [rangeset]
 *      - Fill the blocks with data read from the new_data file.
 *
 *    erase [rangeset]
 *      - Mark the given blocks as empty.
 *
 *    move <...>
 *    bsdiff <patchstart> <patchlen> <...>
 *    imgdiff <patchstart> <patchlen> <...>
 *      - Read the source blocks, apply a patch (or not in the case of move), write result to target
 *      blocks.  bsdiff or imgdiff specifies the type of patch; move means no patch at all.
 *
 *        See the comments in LoadSrcTgtVersion3() for a description of the <...> format.
 *
 *    stash <stash_id> <src_range>
 *      - Load the given source range and stash the data in the given slot of the stash table.
 *
 *    free <stash_id>
 *      - Free the given stash data.
 *
 * The creator of the transfer list will guarantee that no block is read (ie, used as the source for
 * a patch or move) after it has been written.
 // 创建transfer list时会保证 一个stash在stash命令中的加载 会放在被move/bsdiff/imgdiff命令使用此stash之前
// v2中,支持一个新命令stash, stash将从source img中读取的数据,保存到
// 分配的内存"stash table", 随后会 用stash table中刚存储的项去填充
// source data中丢失的字节位,因为这些字节位在执行move/bsdiff/imgdiff
// 时是不允许去读的
// 这会产生更小的升级包,因为我们可以通过把数据存储到别处然后以后使用的方式, 
// 来到达 按pieces是怎么更新的顺序 来组织
// 而不是一点都不使用 作为输入的数据来对系统打patch
 *
 * The creator will guarantee that a given stash is loaded (with a stash command) before it's used
 * in a move/bsdiff/imgdiff command.
 *
 * Within one command the source and target ranges may overlap so in general we need to read the
 * entire source into memory before writing anything to the target blocks.
 *
 * All the patch data is concatenated into one patch_data file in the update package. It must be
 * stored uncompressed because we memory-map it in directly from the archive. (Since patches are
 * already compressed, we lose very little by not compressing their concatenation.)
 *
 * Commands that read data from the partition (i.e. move/bsdiff/imgdiff/stash) have one or more
 * additional hashes before the range parameters, which are used to check if the command has already
 * been completed and verify the integrity of the source data.
  // 在V3中,需要从flash分区读取数据的命令(move/bsdiff/imgdiff/stash),
// 在range参数前有一个或多个hash值(sha1),这些hash值用于检查命令是否
// 已经完成,并且验证source data的完整性

//L上支持的命令bsdiff,erase,imgdiff,move,new,zero
//M上增加的命令:stash(v2新增),free(v3新增)
 */

 //block_image_verify("/dev/block/bootdevice/by-name/system", package_extract_file("system.transfer.list"), "system.new.dat", "system.patch.dat")
 //block_image_verify("/dev/block/platform/soc.0/f9824900.sdhci/by-name/system", package_extract_file("system.transfer.list"), "system.new.dat", "system.patch.dat")
Value* BlockImageVerifyFn(const char* name, State* state,
                          const std::vector<std::unique_ptr<Expr>>& argv) {
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
    return PerformBlockImageUpdate(name, state, argv, commands,
                sizeof(commands) / sizeof(commands[0]), true);
}

//block_image_update("/dev/block/platform/soc.0/f9824900.sdhci/by-name/system", package_extract_file("system.transfer.list"), "system.new.dat", "system.patch.dat");
//因此脚本中调用BlockImageUpdateFn时,传给BlockImageUpdateFn的argc是block_image_update的参数个数,
// argv数组的每个值就是block_image_update的各个参数
Value* BlockImageUpdateFn(const char* name, State* state,
                          const std::vector<std::unique_ptr<Expr>>& argv) {
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

    return PerformBlockImageUpdate(name, state, argv, commands,
                sizeof(commands) / sizeof(commands[0]), false);
}

//if (range_sha1("/dev/block/platform/mtk-msdc.0/11230000.msdc0/by-name/syst
//em", "72,1,32770,32929,32931,33439,65535,65536,65538,66046,98303,98304,98306,98465,98467,98975,131071,131072,131074,131582,163839,163840,163842,164001,164003,164511,196607,196608,196610,197118,22
//9375,229376,229378,229537,229539,230047,262143,262144,262146,262654,294911,294912,294914,295073,295075,295583,327679,327680,327682,328190,355086,360448,360450,393216,393218,425984,425986,458752,458754,491520,491522,524288,524290,557056,557058,589824,589826,622592,622594,623102,650190,650191,655320") == "3168346b9a857c0dd0e962e86032bf464a007957" || block_image_verify("/dev/block/platform/mtk-msdc.0/11230000.msdc0/by-name/system", package_extract_file("system.transfer.list"), "system.new.dat", "system.patch.dat")) then
Value* RangeSha1Fn(const char* name, State* state, const std::vector<std::unique_ptr<Expr>>& argv) {
    if (argv.size() != 2) {
        ErrorAbort(state, kArgsParsingFailure, "range_sha1 expects 2 arguments, got %zu",
                   argv.size());
        return StringValue("");
    }

    std::vector<std::unique_ptr<Value>> args;
    // 解析range_sha1的分区路径到blockdev_filename,解析区间范围参数到ranges
    if (!ReadValueArgs(state, argv, &args)) {
        return nullptr;
    }

    const Value* blockdev_filename = args[0].get();
    const Value* ranges = args[1].get();

    if (blockdev_filename->type != VAL_STRING) {
        ErrorAbort(state, kArgsParsingFailure, "blockdev_filename argument to %s must be string",
                   name);
        return StringValue("");
    }
    if (ranges->type != VAL_STRING) {
        ErrorAbort(state, kArgsParsingFailure, "ranges argument to %s must be string", name);
        return StringValue("");
    }

    // 打开/dev/block/platform/mtk-msdc.0/11230000.msdc0/by-name/system设备节点
    android::base::unique_fd fd(ota_open(blockdev_filename->data.c_str(), O_RDWR));
    if (fd == -1) {
        ErrorAbort(state, kFileOpenFailure, "open \"%s\" failed: %s",
                   blockdev_filename->data.c_str(), strerror(errno));
        return StringValue("");
    }

    // ranges->data指向"72,1,32770,32...",将这72个区间段解析后保存到rs
    RangeSet rs = parse_range(ranges->data);

    SHA_CTX ctx;
    SHA1_Init(&ctx);

    // buffer大小刚好是1个block
    std::vector<uint8_t> buffer(BLOCKSIZE);
    // 在外层循环 block区间 的个数次,从而叠加积累每个区间
    // 在for循环中累计更新这72个区间的hash,累计完后一次性计算sha1
    for (size_t i = 0; i < rs.count; ++i) {
        if (!check_lseek(fd, (off64_t)rs.pos[i*2] * BLOCKSIZE, SEEK_SET)) {
            ErrorAbort(state, kLseekFailure, "failed to seek %s: %s",
                       blockdev_filename->data.c_str(), strerror(errno));
            return StringValue("");
        }

		// 这个for中更新每个区间内所有block的hash
		// 在里层for循环中处理每个区间,一次读入一个block到buffer并更新ctx, 循环次数为这个block区间的大小
        for (size_t j = rs.pos[i*2]; j < rs.pos[i*2+1]; ++j) {
            //每循环一次读取1个block,并更新hash
            if (read_all(fd, buffer, BLOCKSIZE) == -1) {
                ErrorAbort(state, kFreadFailure, "failed to read %s: %s",
                           blockdev_filename->data.c_str(), strerror(errno));
                return StringValue("");
            }

            SHA1_Update(&ctx, buffer.data(), BLOCKSIZE);
        }
    }
    uint8_t digest[SHA_DIGEST_LENGTH];
    //计算所有block区间叠加起来的sha
    // digest就是最终这72个区间的sha1,range_sha1返回digest的值,在if中和3168346b9a857c0dd0e962e86032bf464a007957比较
    SHA1_Final(digest, &ctx);

    // 返回Value格式的sha, 返回的value的type字段为VAL_STRING
    return StringValue(print_sha1(digest));
}

// This function checks if a device has been remounted R/W prior to an incremental
// OTA update. This is an common cause of update abortion. The function reads the
// 1st block of each partition and check for mounting time/count. It return string "t"
// if executes successfully and an empty string otherwise.

Value* CheckFirstBlockFn(const char* name, State* state,
                         const std::vector<std::unique_ptr<Expr>>& argv) {
     if (argv.size() != 1) {
        ErrorAbort(state, kArgsParsingFailure, "check_first_block expects 1 argument, got %zu",
                   argv.size());
        return StringValue("");
    }

    std::vector<std::unique_ptr<Value>> args;
    if (!ReadValueArgs(state, argv, &args)) {
        return nullptr;
    }

    const Value* arg_filename = args[0].get();

    if (arg_filename->type != VAL_STRING) {
        ErrorAbort(state, kArgsParsingFailure, "filename argument to %s must be string", name);
        return StringValue("");
    }

    android::base::unique_fd fd(ota_open(arg_filename->data.c_str(), O_RDONLY));
    if (fd == -1) {
        ErrorAbort(state, kFileOpenFailure, "open \"%s\" failed: %s", arg_filename->data.c_str(),
                   strerror(errno));
        return StringValue("");
    }

    RangeSet blk0 {1 /*count*/, 1/*size*/, std::vector<size_t> {0, 1}/*position*/};
    std::vector<uint8_t> block0_buffer(BLOCKSIZE);

    if (ReadBlocks(blk0, block0_buffer, fd) == -1) {
        ErrorAbort(state, kFreadFailure, "failed to read %s: %s", arg_filename->data.c_str(),
                strerror(errno));
        return StringValue("");
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

    return StringValue("t");
}


Value* BlockImageRecoverFn(const char* name, State* state,
                           const std::vector<std::unique_ptr<Expr>>& argv) {
    if (argv.size() != 2) {
        ErrorAbort(state, kArgsParsingFailure, "block_image_recover expects 2 arguments, got %zu",
                   argv.size());
        return StringValue("");
    }

    std::vector<std::unique_ptr<Value>> args;
    if (!ReadValueArgs(state, argv, &args)) {
        return nullptr;
    }

    const Value* filename = args[0].get();
    const Value* ranges = args[1].get();

    if (filename->type != VAL_STRING) {
        ErrorAbort(state, kArgsParsingFailure, "filename argument to %s must be string", name);
        return StringValue("");
    }
    if (ranges->type != VAL_STRING) {
        ErrorAbort(state, kArgsParsingFailure, "ranges argument to %s must be string", name);
        return StringValue("");
    }

    // Output notice to log when recover is attempted
    LOG(INFO) << filename->data << " image corrupted, attempting to recover...";

    // When opened with O_RDWR, libfec rewrites corrupted blocks when they are read
    fec::io fh(filename->data.c_str(), O_RDWR);

    if (!fh) {
        ErrorAbort(state, kLibfecFailure, "fec_open \"%s\" failed: %s", filename->data.c_str(),
                   strerror(errno));
        return StringValue("");
    }

    if (!fh.has_ecc() || !fh.has_verity()) {
        ErrorAbort(state, kLibfecFailure, "unable to use metadata to correct errors");
        return StringValue("");
    }

    fec_status status;

    if (!fh.get_status(status)) {
        ErrorAbort(state, kLibfecFailure, "failed to read FEC status");
        return StringValue("");
    }

    RangeSet rs = parse_range(ranges->data);

    uint8_t buffer[BLOCKSIZE];

    for (size_t i = 0; i < rs.count; ++i) {
        for (size_t j = rs.pos[i * 2]; j < rs.pos[i * 2 + 1]; ++j) {
            // Stay within the data area, libfec validates and corrects metadata
            if (status.data_size <= (uint64_t)j * BLOCKSIZE) {
                continue;
            }

            if (fh.pread(buffer, BLOCKSIZE, (off64_t)j * BLOCKSIZE) != BLOCKSIZE) {
                ErrorAbort(state, kLibfecFailure, "failed to recover %s (block %zu): %s",
                           filename->data.c_str(), j, strerror(errno));
                return StringValue("");
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
    LOG(INFO) << "..." << filename->data << " image recovered successfully.";
    return StringValue("t");
}

void RegisterBlockImageFunctions() {
    RegisterFunction("block_image_verify", BlockImageVerifyFn);
    RegisterFunction("block_image_update", BlockImageUpdateFn);
    RegisterFunction("block_image_recover", BlockImageRecoverFn);
    RegisterFunction("check_first_block", CheckFirstBlockFn);
    RegisterFunction("range_sha1", RangeSha1Fn);
}
