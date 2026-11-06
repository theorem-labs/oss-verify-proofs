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

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <curl/curl.h>

#include <fuzzer/FuzzedDataProvider.h>
#include "fuzz_bufq.h"

extern "C" {
#include "bufq.h"
}

/**
 * Template buffer.  This buffer is precomputed for performance and used as a
 * cyclic pattern of 0, 1, ..., 255, 0, ... when reading and writing. It can be
 * useful to detect unexpected data shifting or corruption. It is a constant
 * table, so it lives in read-only program data and cannot be written by
 * mistake: a write to it faults, as a write to a read-only mapping would.
 * Building it at compile time also means the harness needs no system call to
 * set it up.
 */
#define TEMPLATE_4(n)  (n), (n) + 1, (n) + 2, (n) + 3
#define TEMPLATE_16(n) TEMPLATE_4(n), TEMPLATE_4((n) + 4), \
                       TEMPLATE_4((n) + 8), TEMPLATE_4((n) + 12)
#define TEMPLATE_64(n) TEMPLATE_16(n), TEMPLATE_16((n) + 16), \
                       TEMPLATE_16((n) + 32), TEMPLATE_16((n) + 48)
#define TEMPLATE_256   TEMPLATE_64(0), TEMPLATE_64(64), \
                       TEMPLATE_64(128), TEMPLATE_64(192)
#define TEMPLATE_X2(...)    __VA_ARGS__, __VA_ARGS__
#define TEMPLATE_X4(...)    TEMPLATE_X2(TEMPLATE_X2(__VA_ARGS__))
#define TEMPLATE_X16(...)   TEMPLATE_X4(TEMPLATE_X4(__VA_ARGS__))
#define TEMPLATE_X256(...)  TEMPLATE_X16(TEMPLATE_X16(__VA_ARGS__))
#define TEMPLATE_X1024(...) TEMPLATE_X4(TEMPLATE_X256(__VA_ARGS__))

static_assert(FUZZ_MAX_RW_SIZE == 1024 * 256,
              "template_buffer holds FUZZ_MAX_RW_SIZE + 256 bytes "
              "as 1025 copies of 0..255");

static const unsigned char template_buffer[FUZZ_MAX_RW_SIZE + 256] = {
  TEMPLATE_X1024(TEMPLATE_256), TEMPLATE_256
};

/*
 * Compute a pointer to a read-only buffer with our pattern, knowing that the
 * first byte to appear is next_byte.
 */
static const unsigned char *compute_buffer(unsigned char next_byte,
                                           const unsigned char *buf) {
  return buf + next_byte;
}

struct writer_cb_ctx {
  bool verbose;
  const unsigned char *template_buf;
  size_t read_len;
  unsigned char next_byte_read;
};

/**
 * Consume and verify up to read_len from a BUFQ via callback for Curl_bufq_pass.
 */
CURLcode bufq_writer_cb(void *writer_ctx,
                       const unsigned char *buf, size_t len,
                       size_t *pnwritten)
{
  struct writer_cb_ctx *ctx = (struct writer_cb_ctx *)writer_ctx;

  *pnwritten = 0;
  if (ctx->read_len <= 0)
    return CURLE_AGAIN;

  FV_PRINTF(ctx->verbose, "Writer CB: %zu space available, %zu pending\n", len, ctx->read_len);

  *pnwritten = len > ctx->read_len ? ctx->read_len : len;

  const unsigned char *compare = compute_buffer(ctx->next_byte_read, ctx->template_buf);
  assert(memcmp(buf, compare, *pnwritten) == 0);
  ctx->next_byte_read += *pnwritten;
  ctx->read_len -= *pnwritten;

  return CURLE_OK;
}

struct reader_cb_ctx {
  bool verbose;
  const unsigned char *template_buf;
  size_t write_len;
  unsigned char next_byte_write;
};

/**
 * Write up to write_len to a BUFQ via callback for Curl_bufq_slurp/sipn.
 */
static CURLcode bufq_reader_cb(void *reader_ctx,
                              unsigned char *buf, size_t len,
                              size_t *pnread)
{
  struct reader_cb_ctx *ctx = (struct reader_cb_ctx *)reader_ctx;

  *pnread = 0;
  if (ctx->write_len <= 0)
    return CURLE_AGAIN;

  FV_PRINTF(ctx->verbose, "Reader CB: %zu space available, %zu pending\n", len, ctx->write_len);

  *pnread = len > ctx->write_len ? ctx->write_len : len;

  const unsigned char *compare = compute_buffer(ctx->next_byte_write, ctx->template_buf);
  memcpy(buf, compare, *pnread);
  ctx->next_byte_write += *pnread;
  ctx->write_len -= *pnread;

  return CURLE_OK;
}

/**
 * Function for handling the operations
 */
int fuzz_handle_bufq(FuzzedDataProvider *fuzz)
{
  static bool verbose = (getenv("FUZZ_VERBOSE") != NULL);
  const unsigned char *template_buf = template_buffer;

  struct bufq q;
  struct bufc_pool pool;

  /* Prepare basic configuration values */
  int max_chunks = fuzz->ConsumeIntegralInRange(1, FUZZ_MAX_CHUNKS_QTY);
  int chunk_size = fuzz->ConsumeIntegralInRange(1, FUZZ_MAX_CHUNK_SIZE);
  bool use_pool = fuzz->ConsumeBool();
  bool no_spare = fuzz->ConsumeBool();
  int max_spare = fuzz->ConsumeIntegralInRange(1, FUZZ_MAX_MAX_SPARE);

  FV_PRINTF(verbose, "Begin fuzzing!\n");

  if (use_pool) {
    FV_PRINTF(verbose, "Using pool init\n");
    Curl_bufcp_init(&pool, chunk_size, max_spare);
    Curl_bufq_initp(&q, &pool, max_chunks, no_spare ? BUFQ_OPT_NO_SPARES : BUFQ_OPT_NONE);
  } else {
    FV_PRINTF(verbose, "Using normal init\n");
    Curl_bufq_init(&q, chunk_size, max_chunks);
  }

  size_t buffer_bytes = 0;
  unsigned char next_byte_read = 0;
  unsigned char next_byte_write = 0;
  while (fuzz->remaining_bytes() > 0) {
    CURLcode err = CURLE_OK;
    uint32_t op_type = fuzz->ConsumeIntegralInRange(0, OP_TYPE_MAX);

    assert(Curl_bufq_is_empty(&q) == !buffer_bytes);
    assert(Curl_bufq_len(&q) == buffer_bytes);

    switch (op_type) {
      case OP_TYPE_RESET: {
        FV_PRINTF(verbose, "OP: reset\n");
        Curl_bufq_reset(&q);
        buffer_bytes = 0;
        next_byte_read = next_byte_write;
        break;
      }

      case OP_TYPE_PEEK: {
        FV_PRINTF(verbose, "OP: peek\n");
        const unsigned char *pbuf;
        size_t plen;
        bool avail = Curl_bufq_peek(&q, &pbuf, &plen);
        if (avail) {
          const unsigned char *compare = compute_buffer(next_byte_read, template_buf);
          assert(memcmp(pbuf, compare, plen) == 0);
        } else {
          FV_PRINTF(verbose, "OP: peek, error\n");
        }
        break;
      }

      case OP_TYPE_PEEK_AT: {
        size_t op_size = fuzz->ConsumeIntegralInRange(0, FUZZ_MAX_RW_SIZE);
        FV_PRINTF(verbose, "OP: peek at %zu\n", op_size);
        const unsigned char *pbuf;
        size_t plen;
        bool avail = Curl_bufq_peek_at(&q, op_size, &pbuf, &plen);
        if (avail) {
          const unsigned char *compare = compute_buffer(next_byte_read + op_size, template_buf);
          assert(memcmp(pbuf, compare, plen) == 0);
        } else {
          FV_PRINTF(verbose, "OP: peek at, error\n");
        }
        break;
      }

      case OP_TYPE_READ: {
        size_t op_size = fuzz->ConsumeIntegralInRange(0, FUZZ_MAX_RW_SIZE);
        FV_PRINTF(verbose, "OP: read, size %zu\n", op_size);
        unsigned char *buf = (unsigned char *)malloc(op_size * sizeof(*buf));
        size_t read;
        CURLcode result = Curl_bufq_read(&q, buf, op_size, &read);
        if (!result) {
          FV_PRINTF(verbose, "OP: read, success, read %zu, expect begins with %x\n", read, next_byte_read);
          buffer_bytes -= read;
          assert(buffer_bytes >= 0);
          const unsigned char *compare = compute_buffer(next_byte_read, template_buf);
          next_byte_read += read;
          assert(memcmp(buf, compare, read) == 0);
        } else {
          FV_PRINTF(verbose, "OP: read, error\n");
        }
        free(buf);
        break;
      }

      case OP_TYPE_SLURP: {
        size_t op_size = fuzz->ConsumeIntegralInRange(0, FUZZ_MAX_RW_SIZE);
        FV_PRINTF(verbose, "OP: slurp, size %zd\n", op_size);
        struct reader_cb_ctx ctx = { .verbose = verbose, .template_buf = template_buf, .write_len = op_size, .next_byte_write = next_byte_write };
        size_t write;
        CURLcode result = Curl_bufq_slurp(&q, bufq_reader_cb, &ctx, &write);
        if (!result) {
          FV_PRINTF(verbose, "OP: slurp, success, wrote %zu, expect begins with %x\n", write, ctx.next_byte_write);
          buffer_bytes += write;
        } else {
          FV_PRINTF(verbose, "OP: slurp, error\n");
          /* in case of -1, it may still have wrote something, adjust for that */
          buffer_bytes += (op_size - ctx.write_len);
        }
        assert(buffer_bytes <= chunk_size * max_chunks);
        next_byte_write = ctx.next_byte_write;
        break;
      }

      case OP_TYPE_SIPN: {
        size_t op_size = fuzz->ConsumeIntegralInRange(0, FUZZ_MAX_RW_SIZE);
        FV_PRINTF(verbose, "OP: sipn, size %zd\n", op_size);
        struct reader_cb_ctx ctx = { .verbose = verbose, .template_buf = template_buf, .write_len = op_size, .next_byte_write = next_byte_write };
        size_t write;
        CURLcode result = Curl_bufq_sipn(&q, op_size, bufq_reader_cb, &ctx, &write);
        if (!result) {
          FV_PRINTF(verbose, "OP: sipn, success, wrote %zu, expect begins with %x\n", write, ctx.next_byte_write);
          buffer_bytes += write;
          assert(buffer_bytes <= chunk_size * max_chunks);
          next_byte_write = ctx.next_byte_write;
        } else {
          FV_PRINTF(verbose, "OP: sipn, error\n");
        }
        break;
      }

      case OP_TYPE_PASS: {
        size_t op_size = fuzz->ConsumeIntegralInRange(0, FUZZ_MAX_RW_SIZE);
        FV_PRINTF(verbose, "OP: pass, size %zd\n", op_size);
        struct writer_cb_ctx ctx = { .verbose = verbose, .template_buf = template_buf, .read_len = op_size, .next_byte_read = next_byte_read };
        size_t nread;
        CURLcode result = Curl_bufq_pass(&q, bufq_writer_cb, &ctx, &nread);
        if (!result) {
          FV_PRINTF(verbose, "OP: pass, success, read %zu, expect begins with %x\n", nread, ctx.next_byte_read);
          buffer_bytes -= nread;
        } else {
          FV_PRINTF(verbose, "OP: pass, error\n");
          /* in case of -1, it may still have read something, adjust for that */
          buffer_bytes -= (op_size - ctx.read_len);
        }
        assert(buffer_bytes >= 0);
        next_byte_read = ctx.next_byte_read;
        break;
      }

      case OP_TYPE_SKIP: {
        size_t op_size = fuzz->ConsumeIntegralInRange(0, FUZZ_MAX_RW_SIZE);
        FV_PRINTF(verbose, "OP: skip, size %zu\n", op_size);
        Curl_bufq_skip(&q, op_size);
        size_t old_buffer_bytes = buffer_bytes;
        buffer_bytes = old_buffer_bytes > op_size ? old_buffer_bytes - op_size : 0;
        next_byte_read += old_buffer_bytes > op_size ? op_size : old_buffer_bytes;
        break;
      }

      case OP_TYPE_WRITE: {
        size_t op_size = fuzz->ConsumeIntegralInRange(0, FUZZ_MAX_RW_SIZE);
        FV_PRINTF(verbose, "OP: write, size %zu, begins with %x\n", op_size, next_byte_write);
        const unsigned char *buf = compute_buffer(next_byte_write, template_buf);
        size_t written;
        CURLcode result = Curl_bufq_write(&q, buf, op_size, &written);
        if (!result) {
          FV_PRINTF(verbose, "OP: write, success, written %zu\n", written);
          next_byte_write += written;
          buffer_bytes += written;
          assert(buffer_bytes <= chunk_size * max_chunks);
        } else {
          FV_PRINTF(verbose, "OP: write, error\n");
        }
        break;
      }

      default: {
        /* Should never happen */
        assert(false);
      }
    }
  }

  Curl_bufq_free(&q);
  if (use_pool)
  {
    Curl_bufcp_free(&pool);
  }

  return 0;
}

/**
 * Fuzzing entry point. This function is passed a buffer containing a test
 * case.  This test case should drive the cURL API into making a series of
 * BUFQ operations.
 */
extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)
{
  FuzzedDataProvider fuzzed_data(data, size);

  /* Run the operations */
  fuzz_handle_bufq(&fuzzed_data);

  /* This function must always return 0. Non-zero codes are reserved. */
  return 0;
}
