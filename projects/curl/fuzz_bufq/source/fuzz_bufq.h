/***************************************************************************
 *                                  _   _ ____  _
 *  Project                     ___| | | |  _ \| |
 *                             / __| | | | |_) | |
 *                            | (__| |_| |  _ <| |___
 *                             \___|\___/|_| \_\_____|
 *
 * Copyright (C) Max Dymond, <cmeister2@gmail.com>, et al.
 *
 * This software is licensed as described in the file COPYING, which
 * you should have received as part of this distribution. The terms
 * are also available at https://curl.se/docs/copyright.html.
 *
 * You may opt to use, copy, modify, merge, publish, distribute and/or sell
 * copies of the Software, and permit persons to whom the Software is
 * furnished to do so, under the terms of the COPYING file.
 *
 * This software is distributed on an "AS IS" basis, WITHOUT WARRANTY OF ANY
 * KIND, either express or implied.
 *
 ***************************************************************************/

/**
 * Limits for fields
 */
#define FUZZ_MAX_CHUNK_SIZE      (16 * 1024)
#define FUZZ_MAX_CHUNKS_QTY      16
#define FUZZ_MAX_MAX_SPARE       16
#define FUZZ_MAX_RW_SIZE         (FUZZ_MAX_CHUNKS_QTY * FUZZ_MAX_CHUNK_SIZE)

/**
 * Operation identifiers
 */
#define OP_TYPE_WRITE           0
#define OP_TYPE_READ            1
#define OP_TYPE_SKIP            2
#define OP_TYPE_RESET           3
#define OP_TYPE_PEEK            4
#define OP_TYPE_PEEK_AT         5
#define OP_TYPE_SIPN            6
#define OP_TYPE_SLURP           7
#define OP_TYPE_PASS            8
#define OP_TYPE_MAX             8

/**
 * Helper macros
 */

#define FV_PRINTF(verbose, ...)                                               \
        if(!!(verbose)) {                                                     \
          printf(__VA_ARGS__);                                                \
        }
