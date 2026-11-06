#!/bin/bash -eu
# Copyright 2026 Pau Aliagas <linuxnow@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Builds libreac's nine fuzz targets (fuzz/fuzz_*.c in the libreac repository) into $OUT.
# libreac's own Makefile builds them with a native clang and libFuzzer; this script makes the same
# harnesses into static riscv64 programs, each linked against a static libreac.a of this build.

# The library: every source in src/, compiled with this build's flags, in a fixed order.
mkdir -p "$WORK/obj"
objs=()
for src in $(LC_ALL=C ls src/*.c); do
  obj="$WORK/obj/$(basename "$src" .c).o"
  $CC $CFLAGS -std=c11 -Iinclude -c "$src" -o "$obj"
  objs+=("$obj")
done
$AR rcs "$WORK/libreac.a" "${objs[@]}"

# The fuzz targets.
for h in decode ctrl identity disco scene boxreg knock grant; do
  $CC $CFLAGS -std=c11 -Iinclude -Ifuzz -c "fuzz/fuzz_$h.c" -o "$WORK/fuzz_$h.o"
  $CC $CFLAGS "$WORK/fuzz_$h.o" -o "$OUT/fuzz_$h" $LIB_FUZZING_ENGINE "$WORK/libreac.a" -lm
done

# fuzz_pcap. pcap_source_open() takes a path and calls fopen(); the harness answers its one path with
# fmemopen() over the input. libreac's Makefile does this with -Wl,--wrap=fopen, but the sealed
# AddressSanitizer runtime defines __wrap_fopen itself, so the two collide in the asan builds. Here the
# same redirection is made by name, in all four builds: the reader's fopen and the harness's
# __wrap_fopen both become libreac_fuzz_fopen, and the harness's __real_fopen is fopen. The reader is
# compiled a second time for this, into its own object, which the link takes before libreac.a; neither
# source file changes.
$CC $CFLAGS -std=c11 -Iinclude -Dfopen=libreac_fuzz_fopen -c src/pcap_source.c -o "$WORK/pcap_source_fuzz.o"
$CC $CFLAGS -std=c11 -Iinclude -Ifuzz -D__wrap_fopen=libreac_fuzz_fopen -D__real_fopen=fopen \
  -c fuzz/fuzz_pcap.c -o "$WORK/fuzz_pcap.o"
$CC $CFLAGS "$WORK/fuzz_pcap.o" "$WORK/pcap_source_fuzz.o" -o "$OUT/fuzz_pcap" $LIB_FUZZING_ENGINE \
  "$WORK/libreac.a" -lm
