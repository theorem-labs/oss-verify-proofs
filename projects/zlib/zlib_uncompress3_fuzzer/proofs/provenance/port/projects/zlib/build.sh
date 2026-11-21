#!/bin/sh -e
# Generated from the build recipe of the oss-fuzz-theorems 2026.10 release; do not edit.
#
# Builds the fuzz targets of zlib into $OUT, each from the pin of the release's target for it.
# compile runs build.sh with bash; the release ran each target's build with sh -e, and so does this.
[ -z "${BASH_VERSION:-}" ] || exec sh -e "$0"
. /usr/local/lib/oss-verify/release-target.sh

# checksum_fuzzer: the release's target zlib-checksum_fuzzer
(
ov_target_begin zlib-checksum_fuzzer
build_lib() {
  oft_build_cmake
  oft_build_harness "checksum_fuzzer.c"
  oft_seal_getenv
  oft_seal_mkstemp
  oft_seal_getpid
}
LIB_ARCHIVE="lib/liboft.a"
LIB_CFLAGS=""
ov_target_build checksum_fuzzer
)

# compress_fuzzer: the release's target zlib-compress_fuzzer
(
ov_target_begin zlib-compress_fuzzer
build_lib() {
  oft_build_cmake
  oft_build_harness "compress_fuzzer.c"
  oft_seal_getenv
  oft_seal_mkstemp
  oft_seal_getpid
}
LIB_ARCHIVE="lib/liboft.a"
LIB_CFLAGS=""
ov_target_build compress_fuzzer
)

# example_dict_fuzzer: the release's target zlib-example_dict_fuzzer
(
ov_target_begin zlib-example_dict_fuzzer
build_lib() {
  oft_build_cmake
  oft_build_harness "example_dict_fuzzer.c"
  oft_seal_getenv
  oft_seal_mkstemp
  oft_seal_getpid
}
LIB_ARCHIVE="lib/liboft.a"
LIB_CFLAGS=""
ov_target_build example_dict_fuzzer
)

# example_flush_fuzzer: the release's target zlib-example_flush_fuzzer
(
ov_target_begin zlib-example_flush_fuzzer
build_lib() {
  oft_build_cmake
  oft_build_harness "example_flush_fuzzer.c"
  oft_seal_getenv
  oft_seal_mkstemp
  oft_seal_getpid
}
LIB_ARCHIVE="lib/liboft.a"
LIB_CFLAGS=""
ov_target_build example_flush_fuzzer
)

# example_large_fuzzer: the release's target zlib-example_large_fuzzer
(
ov_target_begin zlib-example_large_fuzzer
build_lib() {
  oft_build_cmake
  oft_build_harness "example_large_fuzzer.c"
  oft_seal_getenv
  oft_seal_mkstemp
  oft_seal_getpid
}
LIB_ARCHIVE="lib/liboft.a"
LIB_CFLAGS=""
ov_target_build example_large_fuzzer
)

# example_small_fuzzer: the release's target zlib-example_small_fuzzer
(
ov_target_begin zlib-example_small_fuzzer
build_lib() {
  oft_build_cmake
  oft_build_harness "example_small_fuzzer.c"
  oft_seal_getenv
  oft_seal_mkstemp
  oft_seal_getpid
}
LIB_ARCHIVE="lib/liboft.a"
LIB_CFLAGS=""
ov_target_build example_small_fuzzer
)

# gzio_fuzzer: the release's target zlib-gzio_fuzzer
(
ov_target_begin zlib-gzio_fuzzer
build_lib() {
  oft_build_cmake
  # gzio_fuzzer.c calls close(), which is declared in unistd.h; zlib 1.4's headers do not include it.
  OFT_HARNESS_CFLAGS="-include unistd.h" oft_build_harness "gzio_fuzzer.c"
  oft_seal_getenv
  oft_seal_mkstemp
  oft_seal_getpid
}
LIB_ARCHIVE="lib/liboft.a"
LIB_CFLAGS=""
ov_target_build gzio_fuzzer
)

# minigzip_fuzzer: the release's target zlib-minigzip_fuzzer
(
ov_target_begin zlib-minigzip_fuzzer
build_lib() {
  oft_build_cmake
  oft_build_harness "minigzip_fuzzer.c"
  oft_seal_getenv
  oft_seal_mkstemp
  oft_seal_getpid
}
LIB_ARCHIVE="lib/liboft.a"
LIB_CFLAGS=""
ov_target_build minigzip_fuzzer
)

# zlib_uncompress2_fuzzer: the release's target zlib-zlib_uncompress2_fuzzer
(
ov_target_begin zlib-zlib_uncompress2_fuzzer
build_lib() {
  oft_require_target_cxx
  oft_build_cmake
  oft_build_harness "zlib_uncompress2_fuzzer.cc"
  oft_seal_getenv
  oft_seal_mkstemp
  oft_seal_getpid
}
LIB_ARCHIVE="lib/liboft.a"
LIB_CFLAGS=""
ov_target_build zlib_uncompress2_fuzzer
)

# zlib_uncompress3_fuzzer: the release's target zlib-zlib_uncompress3_fuzzer
(
ov_target_begin zlib-zlib_uncompress3_fuzzer
build_lib() {
  oft_require_target_cxx
  oft_build_cmake
  oft_build_harness "zlib_uncompress3_fuzzer.cc"
  oft_seal_getenv
  oft_seal_mkstemp
  oft_seal_getpid
}
LIB_ARCHIVE="lib/liboft.a"
LIB_CFLAGS=""
ov_target_build zlib_uncompress3_fuzzer
)

# zlib_uncompress_fuzzer: the release's target zlib-zlib_uncompress_fuzzer
(
ov_target_begin zlib-zlib_uncompress_fuzzer
build_lib() {
  oft_require_target_cxx
  oft_build_cmake
  oft_build_harness "zlib_uncompress_fuzzer.cc"
  oft_seal_getenv
  oft_seal_mkstemp
  oft_seal_getpid
}
LIB_ARCHIVE="lib/liboft.a"
LIB_CFLAGS=""
ov_target_build zlib_uncompress_fuzzer
)
