/*
 * Copyright (C) 2009 The Android Open Source Project
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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <memory>
#include <vector>

#include "applypatch.h"
#include "edify/expr.h"
#include "openssl/sha.h"

static int CheckMode(int argc, char** argv) {
    if (argc < 3) {
        return 2;
    }
    return applypatch_check(argv[2], argc-3, argv+3);
}

static int SpaceMode(int argc, char** argv) {
    if (argc != 3) {
        return 2;
    }
    char* endptr;
    size_t bytes = strtol(argv[2], &endptr, 10);
    if (bytes == 0 && endptr == argv[2]) {
        printf("can't parse \"%s\" as byte count\n\n", argv[2]);
        return 1;
    }
    return CacheSizeCheck(bytes);
}

// Parse arguments (which should be of the form "<sha1>:<filename>"
// into the new parallel arrays *sha1s and *files.Returns true on
// success.
static bool ParsePatchArgs(int argc, char** argv, std::vector<char*>* sha1s,
                           std::vector<FileContents>* files) {
    uint8_t digest[SHA_DIGEST_LENGTH];

    for (int i = 0; i < argc; ++i) {
        char* colon = strchr(argv[i], ':');
        if (colon == nullptr) {
            printf("no ':' in patch argument \"%s\"\n", argv[i]);
            return false;
        }
        *colon = '\0';
        ++colon;
        if (ParseSha1(argv[i], digest) != 0) {
            printf("failed to parse sha1 \"%s\"\n", argv[i]);
            return false;
        }

        sha1s->push_back(argv[i]);
        FileContents fc;
        if (LoadFileContents(colon, &fc) != 0) {
            return false;
        }
        files->push_back(std::move(fc));
    }
    return true;
}

static int FlashMode(const char* src_filename, const char* tgt_filename,
                     const char* tgt_sha1, size_t tgt_size) {
    return applypatch_flash(src_filename, tgt_filename, tgt_sha1, tgt_size);
}

static int PatchMode(int argc, char** argv) {
    FileContents bonusFc;
    Value bonusValue;
    Value* bonus = nullptr;

    if (argc >= 3 && strcmp(argv[1], "-b") == 0) {
        if (LoadFileContents(argv[2], &bonusFc) != 0) {
            printf("failed to load bonus file %s\n", argv[2]);
            return 1;
        }
        bonus = &bonusValue;
        bonus->type = VAL_BLOB;
        bonus->size = bonusFc.data.size();
        bonus->data = reinterpret_cast<char*>(bonusFc.data.data());
        argc -= 2;
        argv += 2;
    }

    if (argc < 4) {
        return 2;
    }

    char* endptr;
    size_t target_size = strtol(argv[4], &endptr, 10);
    //调用PatchMode传入的代表targetfile的大小的argv[4]字符串解析出来的数值无效
    if (target_size == 0 && endptr == argv[4]) {
        printf("can't parse \"%s\" as byte count\n\n", argv[4]);
        return 1;
    }

    // If no <src-sha1>:<patch> is provided, it is in flash mode.
    if (argc == 5) {
        if (bonus != nullptr) {
            printf("bonus file not supported in flash mode\n");
            return 1;
        }
        return FlashMode(argv[1], argv[2], argv[3], target_size);
    }
    std::vector<char*> sha1s;
    std::vector<FileContents> files;
    //从argv[5]及其以后都是 sha:文件路径 或 sha 的一串数组，调用ParsePatchArgs将这串数组个数保存到num_patches中，
    //将其中所有的sha保存到sha1s指向的数组中， argv[5]及其以后的所有patch文件内容保存在patches[i].data指向的数组中
    if (!ParsePatchArgs(argc-5, argv+5, &sha1s, &files)) {
        printf("failed to parse patch args\n");
        return 1;
    }
    std::vector<Value> patches(files.size());
    std::vector<Value*> patch_ptrs(files.size());
    for (size_t i = 0; i < files.size(); ++i) {
        patches[i].type = VAL_BLOB;
        patches[i].size = files[i].data.size();
        patches[i].data = reinterpret_cast<char*>(files[i].data.data());
        patch_ptrs[i] = &patches[i];
    }
    // 调用applypatch的参数: argv[1]--oldfile, argv[2]--newfile argv[3]--newfilesha1 
    return applypatch(argv[1], argv[2], argv[3], target_size,
                      patch_ptrs.size(), sha1s.data(),
                      patch_ptrs.data(), bonus);
}

// This program applies binary patches to files in a way that is safe
// (the original file is not touched until we have the desired
// replacement for it) and idempotent (it's okay to run this program
// multiple times).
//
// - if the sha1 hash of <tgt-file> is <tgt-sha1>, does nothing and exits
//   successfully.
//
// - otherwise, if no <src-sha1>:<patch> is provided, flashes <tgt-file> with
//   <src-file>. <tgt-file> must be a partition name, while <src-file> must
//   be a regular image file. <src-file> will not be deleted on success.
//
// - otherwise, if the sha1 hash of <src-file> is <src-sha1>, applies the
//   bsdiff <patch> to <src-file> to produce a new file (the type of patch
//   is automatically detected from the file header).  If that new
//   file has sha1 hash <tgt-sha1>, moves it to replace <tgt-file>, and
//   exits successfully.  Note that if <src-file> and <tgt-file> are
//   not the same, <src-file> is NOT deleted on success.  <tgt-file>
//   may be the string "-" to mean "the same as src-file".
//
// - otherwise, or if any error is encountered, exits with non-zero
//   status.
//
// <src-file> (or <file> in check mode) may refer to an MTD partition
// to read the source data.  See the comments for the
// LoadMTDContents() function above for the format of such a filename.

/*applypatch下的Android.mk中会生成
1 libapplypatch 这个是真正供updater升级时调用的
2 applypatch applypatch_static 这两个是完整的可执行文件,主要是用来供recovery\applypatch下的测试脚本applypatch.sh调用
3 imgdiff

applypatch.sh  测试applypatch下的Android.mk中编出来的applypatch
脚本先将applypatch push到手机的/system下,脚本中的run_command函数是adb shell命令的封装
一 # --------------- check mode ----------------------
run_command $WORK_DIR/applypatch -c $WORK_DIR/old.file $OLD_SHA1 || fail
applypatch -c参数
applypatch -c old.file sha1(sha1 是 old.file这个文件的sha1) [sha2  ...]
-c后可以跟多个sha1值,其中有一个是old.file的sha1

applypatch中还有
testname "check mode cache (corrupted) single"
run_command $WORK_DIR/applypatch -c $WORK_DIR/old.file $OLD_SHA1 || fail
testname "check mode cache (missing) single"
run_command $WORK_DIR/applypatch -c $WORK_DIR/old.file $OLD_SHA1 || fail
说明applypatch_check要检查的文件如果确实或者损坏，都会去检查cache下的拷贝的sha1是否匹配
二 # --------------- apply patch ----------------------
run_command $WORK_DIR/applypatch $WORK_DIR/old.file - $NEW_SHA1 $NEW_SIZE $BAD1_SHA1:$WORK_DIR/foo $OLD_SHA1:$WORK_DIR/patch.bsdiff
相当于手机中运行applypatch(argv[0])  /system/old.file(argv[1]) -(argv[2])  newfilesha1(argv[3])  newfilesize(argv[4])  bad_sha1:/system/foo(这个文件内容是“hello”)(argv[5])  oldfilesha1:/system/patch.bsdiff(argv[6]) 
其中-(argv[2]) 通常是由targetfile的路径代替
这将在applypatch的main.c中调用：PatchMode(argc, argv);
*/
int main(int argc, char** argv) {
    if (argc < 2) {
      usage:
        printf(
            "usage: %s [-b <bonus-file>] <src-file> <tgt-file> <tgt-sha1> <tgt-size> "
            "[<src-sha1>:<patch> ...]\n"
            "   or  %s -c <file> [<sha1> ...]\n"
            "   or  %s -s <bytes>\n"
            "   or  %s -l\n"
            "\n"
            "Filenames may be of the form\n"
            "  MTD:<partition>:<len_1>:<sha1_1>:<len_2>:<sha1_2>:...\n"
            "to specify reading from or writing to an MTD partition.\n\n",
            argv[0], argv[0], argv[0], argv[0]);
        return 2;
    }

    int result;

    if (strncmp(argv[1], "-l", 3) == 0) {
        result = ShowLicenses();
    } else if (strncmp(argv[1], "-c", 3) == 0) {
        //因此-c参数执行CheckMode --- applypatch_check(argv[2], argc-3, argv+3);
		//argv[2]这时相当于old.file   argc-3,--要检测的sha值个数, argv+3 指向第一个要检测的sha1
        result = CheckMode(argc, argv);
    } else if (strncmp(argv[1], "-s", 3) == 0) {
        result = SpaceMode(argc, argv);
    } else {
        result = PatchMode(argc, argv);
    }

    if (result == 2) {
        goto usage;
    }
    return result;
}
