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

// See imgdiff.cpp in this directory for a description of the patch file
// format.

#include <applypatch/imgpatch.h>

#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <sys/cdefs.h>
#include <sys/stat.h>
#include <unistd.h>

#include <string>
#include <vector>

#include <applypatch/applypatch.h>
#include <applypatch/imgdiff.h>
#include <android-base/memory.h>
#include <openssl/sha.h>
#include <zlib.h>

static inline int64_t Read8(const void *address) {
  return android::base::get_unaligned<int64_t>(address);
}

static inline int32_t Read4(const void *address) {
  return android::base::get_unaligned<int32_t>(address);
}

// 在GenerateTarget中调用ApplyImagePatch:
// if (header_bytes_read >= 8 && memcmp(header, "IMGDIFF2", 8) == 0) {
//		   result = ApplyImagePatch(source_to_use->data, source_to_use->size, patch, sink, token, &ctx, bonus_data);
// 其中source_to_use->data -- 指向source的实际数据, 
// source_to_use->size -- source实际数据的大小
// patch -- 代表patch的数据机构object
// sink -- ApplyBSDiffPatch中在内存中生成了target的数据, 然后调用sink按对文件还是分区打patch的不同方式保存这些数据
// token -- 最终输出生成target数据的地址
							
// 在BlockImageUpdateFn中在解析imgdiif命令后调用ApplyImagePatch:
// old_data -- buffer -- imgdiif将src rangset中的数据读取到了一段buffer指向的内存中
// __unused
// patch -- patch_value -- 补丁相关数据
// sink -- RangeSinkWrite 
// token -- rss -- 
// ctx -- NULL 
// bonus_data -- NULL 
int ApplyImagePatch(const unsigned char* old_data, ssize_t old_size,
                    const unsigned char* patch_data, ssize_t patch_size,
                    SinkFn sink, void* token) {
  Value patch(VAL_BLOB, std::string(reinterpret_cast<const char*>(patch_data), patch_size));

  return ApplyImagePatch(old_data, old_size, &patch, sink, token, nullptr, nullptr);
}

/*
 * Apply the patch given in 'patch_filename' to the source data given
 * by (old_data, old_size).  Write the patched output to the 'output'
 * file, and update the SHA context with the output data as well.
 * Return 0 on success.
 */
int ApplyImagePatch(const unsigned char* old_data, ssize_t old_size, const Value* patch,
                    SinkFn sink, void* token, SHA_CTX* ctx, const Value* bonus_data) {
  //imgdiff生成的补丁数据,头8字节(magic number and version),之后还有4字节代表chunk count
  if (patch->data.size() < 12) {
    printf("patch too short to contain header\n");
    return -1;
  }

  // IMGDIFF2 uses CHUNK_NORMAL, CHUNK_DEFLATE, and CHUNK_RAW.
  // (IMGDIFF1, which is no longer supported, used CHUNK_NORMAL and
  // CHUNK_GZIP.)
  size_t pos = 12;
  // header指向补丁数据的首地址
  const char* header = &patch->data[0];
  //imgdiff生成的patch,头8字节后还有4字节chunk count
  //patch->size代表补丁数据的长度,如果从BlockImageUpdateFn调用过来,就是bsdiff或imgdiff命令后面第2个参数
  if (memcmp(header, "IMGDIFF2", 8) != 0) {
    printf("corrupt patch file header (magic number)\n");
    return -1;
  }

  //从补丁数据的head后移8字节,读取之后的4个字节,代表chunk count
  int num_chunks = Read4(header + 8);
  // ApplyImagePatch之后就都是在for中循环处理补丁数据中每一个chunk(厚块)
  // 对每个chunk,都是先读出开头4字节的chunk type,然后根据chunk type不同类型在不同条件分支中处理
  for (int i = 0; i < num_chunks; ++i) {
    // each chunk's header record starts with 4 bytes.
    if (pos + 4 > patch->data.size()) {
      printf("failed to read chunk %d record\n", i);
      return -1;
    }
    // 读取每个chunk开始的四字节,代表chunk type
    int type = Read4(&patch->data[pos]);
    pos += 4;

    if (type == CHUNK_NORMAL) {
      // normal_header就是CHUNK_NORMAL类型的chunk自身的头的起始地址
      const char* normal_header = &patch->data[pos];
      pos += 24;
      if (pos > patch->data.size()) {
        printf("failed to read chunk %d normal header data\n", i);
        return -1;
      }

      // 对于CHUNK_NORMAL类型的chunk(厚块)
	  // 补丁数据中chunk type后8+8字节src_start,src_len指定了压缩出这个chunk的源image的section位置
	  // 对于imgdiff命令,源image就是现在升级前android的system分区,因此src_start要和old_data相加才有意义
	  // src_start和src_len都是对old_data指向的数据而言的
      size_t src_start = static_cast<size_t>(Read8(normal_header));
      size_t src_len = static_cast<size_t>(Read8(normal_header + 8));
      // patch_offset就是此chunk在整个imgdiff patch文件的文件头后对应的bsdiff patch格式的数据,
      // 相对整个imgdiff patch的偏移
      size_t patch_offset = static_cast<size_t>(Read8(normal_header + 16));

      if (src_start + src_len > static_cast<size_t>(old_size)) {
        printf("source data too short\n");
        return -1;
      }
      ApplyBSDiffPatch(old_data + src_start, src_len, patch, patch_offset, sink, token, ctx);
    } else if (type == CHUNK_RAW) {
      // raw_header就是CHUNK_RAW类型的chunk自身的头的起始地址
      const char* raw_header = &patch->data[pos];
      pos += 4;
      if (pos > patch->data.size()) {
        printf("failed to read chunk %d raw header data\n", i);
        return -1;
      }

      // 从raw_header开始读取4字节,读到的就是target len
      ssize_t data_len = Read4(raw_header);

      if (pos + data_len > patch->data.size()) {
        printf("failed to read chunk %d raw data\n", i);
        return -1;
      }
      if (ctx) SHA1_Update(ctx, &patch->data[pos], data_len);
      // RAW类型的chunk保存的是target中的数据,因此可以直接写入
      // 将patch->data + pos,也就是raw_header+4开始的target data数据直接写入flash
      if (sink(reinterpret_cast<const unsigned char*>(&patch->data[pos]), data_len, token) !=
          data_len) {
        printf("failed to write chunk %d raw data\n", i);
        return -1;
      }
      // CHUNK_RAW类型的chunk,在其chunk header的target len字段后面直接跟随这个chunk的data
      pos += data_len;
    } else if (type == CHUNK_DEFLATE) {
      // deflate chunks have an additional 60 bytes in their chunk header.
      // deflate类型的chunk,其chunk header一共60字节
      const char* deflate_header = &patch->data[pos];
      pos += 60;
      if (pos > patch->data.size()) {
        printf("failed to read chunk %d deflate header data\n", i);
        return -1;
      }

      size_t src_start = static_cast<size_t>(Read8(deflate_header));
      size_t src_len = static_cast<size_t>(Read8(deflate_header + 8));
      size_t patch_offset = static_cast<size_t>(Read8(deflate_header + 16));
      // expanded len是未压缩的source数据的大小
      size_t expanded_len = static_cast<size_t>(Read8(deflate_header + 24));
      size_t target_len = static_cast<size_t>(Read8(deflate_header + 32));
      int level = Read4(deflate_header + 40);
      int method = Read4(deflate_header + 44);
      int windowBits = Read4(deflate_header + 48);
      int memLevel = Read4(deflate_header + 52);
      int strategy = Read4(deflate_header + 56);

      if (src_start + src_len > static_cast<size_t>(old_size)) {
        printf("source data too short\n");
        return -1;
      }

      // Decompress the source data; the chunk header tells us exactly
      // how big we expect it to be when decompressed.

      // Note: expanded_len will include the bonus data size if
      // the patch was constructed with bonus data.  The
      // deflation will come up 'bonus_size' bytes short; these
      // must be appended from the bonus_data value.
      // DEFLATE类型的chunk,其bspatch格式的补丁数据是已经经过压缩的
      // 判断是否存在bonus data,如果有就取得bonus data大小
      size_t bonus_size = (i == 1 && bonus_data != NULL) ? bonus_data->data.size() : 0;

      // expanded_source指向 申请的存放解压后的source数据的buffer 的起始地址
      std::vector<unsigned char> expanded_source(expanded_len);

      // inflate() doesn't like strm.next_out being a nullptr even with
      // avail_out being zero (Z_STREAM_ERROR).
      if (expanded_len != 0) {
      // 不重要的三个参数:zalloc,zfree,opaque
        z_stream strm;
        strm.zalloc = Z_NULL;
        strm.zfree = Z_NULL;
        strm.opaque = Z_NULL;
        // avail_in:要压缩或解压的数据的长度
        strm.avail_in = src_len;
        // next_in:指向要压缩或解压的数据起始位置的指针,old_data指向的就是source img中的数据
        strm.next_in = old_data + src_start;
        // avail_out:保存压缩或解压后数据的buffer的可用大小,刚开始为申请大小=expanded_len
        strm.avail_out = expanded_len;
        // next_out:指向保存压缩或解压后数据的buffer的指针
        strm.next_out = expanded_source.data();

        //调用zlib的inflateInit:解压初始化的基础函数
        int ret = inflateInit2(&strm, -15);
        if (ret != Z_OK) {
          printf("failed to init source inflation: %d\n", ret);
          return -1;
        }

        // Because we've provided enough room to accommodate the output
        // data, we expect one call to inflate() to suffice.
        // infalte : 解压函数 调用一次inflate解压完source
        ret = inflate(&strm, Z_SYNC_FLUSH);
        if (ret != Z_STREAM_END) {
          printf("source inflation returned %d\n", ret);
          return -1;
        }
        // We should have filled the output buffer exactly, except
        // for the bonus_size.
        // 这时buffer剩余大小应该等于bonus_size
        if (strm.avail_out != bonus_size) {
          printf("source inflation short by %zu bytes\n", strm.avail_out - bonus_size);
          return -1;
        }
        inflateEnd(&strm);

        // 将 bonus拷贝到 存放解压后的source数据的buffer中(expanded_len - bonus_size)地址
        if (bonus_size) {
          memcpy(expanded_source.data() + (expanded_len - bonus_size), &bonus_data->data[0],
                 bonus_size);
        }
      }

      // Next, apply the bsdiff patch (in memory) to the uncompressed data.
      std::vector<unsigned char> uncompressed_target_data;
      // TODO(senj): Remove the only usage of ApplyBSDiffPatchMem here,
      // replace it with ApplyBSDiffPatch with a custom sink function that
      // wraps the given sink function to stream output to save memory.
      // 然后调用ApplyBSDiffPatchMem,对上面得到的uncompressed的source data应用内存中的bsdiff patch 
      if (ApplyBSDiffPatchMem(expanded_source.data(), expanded_len, patch, patch_offset,
                              &uncompressed_target_data) != 0) {
        return -1;
      }
      if (uncompressed_target_data.size() != target_len) {
        printf("expected target len to be %zu, but it's %zu\n", target_len,
               uncompressed_target_data.size());
        return -1;
      }

      // Now compress the target data and append it to the output.

      // we're done with the expanded_source data buffer, so we'll
      // reuse that memory to receive the output of deflate.
      if (expanded_source.size() < 32768U) {
        expanded_source.resize(32768U);
      }

      {
        std::vector<unsigned char>& temp_data = expanded_source;

        // now the deflate stream
        z_stream strm;
        strm.zalloc = Z_NULL;
        strm.zfree = Z_NULL;
        strm.opaque = Z_NULL;
        strm.avail_in = uncompressed_target_data.size();
        strm.next_in = uncompressed_target_data.data();
        int ret = deflateInit2(&strm, level, method, windowBits, memLevel, strategy);
        if (ret != Z_OK) {
          printf("failed to init uncompressed data deflation: %d\n", ret);
          return -1;
        }
        do {
          strm.avail_out = temp_data.size();
          strm.next_out = temp_data.data();
          ret = deflate(&strm, Z_FINISH);
          ssize_t have = temp_data.size() - strm.avail_out;

          if (sink(temp_data.data(), have, token) != have) {
            printf("failed to write %zd compressed bytes to output\n", have);
            return -1;
          }
          if (ctx) SHA1_Update(ctx, temp_data.data(), have);
        } while (ret != Z_STREAM_END);
        deflateEnd(&strm);
      }
    } else {
      printf("patch chunk %d is unknown type %d\n", i, type);
      return -1;
    }
  }

  return 0;
}
