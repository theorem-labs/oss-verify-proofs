#!/bin/bash -eu
# Copyright 2026 Pau Aliagas <linuxnow@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Builds libdiginet's four fuzz targets (fuzz/fuzz_*.c in the libdiginet repository) into $OUT.
# libdiginet's own Makefile builds them with a native clang and libFuzzer; this script makes the
# same harnesses into static riscv64 programs, each linked against a static library of this build.

# The library: the protocol (the frame, the command stream, the controls and the decoder) and the
# session state machine, in a fixed order. The packet socket and the descriptor io
# (transport/src/diginet_io.c) make system calls and read no bytes of their own, so they are not
# built: the session's io is the harness (fuzz/README.md).
mkdir -p "$WORK/obj"
objs=()
for src in src/diginet_frame.c src/diginet_msg.c src/diginet_codec.c src/diginet_decode.c \
           transport/src/diginet_session.c; do
  obj="$WORK/obj/$(basename "$src" .c).o"
  $CC $CFLAGS -std=c11 -D_DEFAULT_SOURCE -Iinclude -c "$src" -o "$obj"
  objs+=("$obj")
done
$AR rcs "$WORK/libdiginet-fuzz.a" "${objs[@]}"

# The fuzz targets.
for h in frame decode codec transport; do
  $CC $CFLAGS -std=c11 -D_DEFAULT_SOURCE -Iinclude -Ifuzz -c "fuzz/fuzz_$h.c" -o "$WORK/fuzz_$h.o"
  $CC $CFLAGS "$WORK/fuzz_$h.o" -o "$OUT/fuzz_$h" $LIB_FUZZING_ENGINE "$WORK/libdiginet-fuzz.a"
done
