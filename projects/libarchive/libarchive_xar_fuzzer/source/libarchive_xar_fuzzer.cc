// Modified by Theorem Labs, 2026-11-14: catch std::bad_alloc from this harness's own allocations, free what it opened and return 0. Ignore SIGPIPE, as libarchive's own bsdtar and bsdcpio do.
/*
 * XAR format specific fuzzer for libarchive
 * Targets xar_read_header and XAR parsing code paths
 */
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <vector>

#include "archive.h"
#include "archive_entry.h"
#include "fuzz_helpers.h"

static constexpr size_t kMaxInputSize = 512 * 1024;  // 512KB



extern "C" int LLVMFuzzerTestOneInput(const uint8_t *buf, size_t len) {
  struct sigaction sa;
  sigemptyset(&sa.sa_mask);
  sa.sa_flags = 0;
  sa.sa_handler = SIG_IGN;
  sigaction(SIGPIPE, &sa, NULL);
  if (len == 0 || len > kMaxInputSize) {
    return 0;
  }

  struct archive *a = archive_read_new();
  if (a == NULL) {
    return 0;
  }

  // Enable XAR format specifically
  archive_read_support_format_xar(a);
  // Enable common filters
  archive_read_support_filter_all(a);

  Buffer buffer = {buf, len, 0};
  if (archive_read_open(a, &buffer, NULL, reader_callback, NULL) != ARCHIVE_OK) {
    archive_read_free(a);
    return 0;
  }

  try {
    std::vector<uint8_t> data_buffer(4096, 0);
    struct archive_entry *entry;

    while (archive_read_next_header(a, &entry) == ARCHIVE_OK) {
      // Exercise entry metadata access
      archive_entry_pathname(entry);
      archive_entry_pathname_w(entry);
      archive_entry_size(entry);
      archive_entry_mtime(entry);
      archive_entry_mode(entry);
      archive_entry_filetype(entry);
      archive_entry_uid(entry);
      archive_entry_gid(entry);

      // Read data
      ssize_t r;
      while ((r = archive_read_data(a, data_buffer.data(), data_buffer.size())) > 0)
        ;
    }
  } catch (const std::bad_alloc &) {
    archive_read_free(a);
    return 0;
  }

  archive_read_free(a);
  return 0;
}
