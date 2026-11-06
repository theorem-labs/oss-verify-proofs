#!/bin/bash -eu
# Copyright 2026 Pau Aliagas <linuxnow@gmail.com>
# SPDX-License-Identifier: Apache-2.0
# Modified 2026 by Theorem Labs, PBC: builds fuzz_preset from the fuzz_preset.c and alloc.c the Dockerfile copies in.
#
# Builds omx-clap-core's three fuzz targets (fuzz/fuzz_*.c in the omx-clap-core repository) into $OUT.
# omx-clap-core's own Makefile builds them with a native clang and libFuzzer; this script makes the same
# harnesses into static riscv64 programs, each linked against a static library of the readers of this
# build.

# The library: the two readers the fuzz targets drive, src/preset_file.c (the preset file and its base64
# state body) and src/lv2_locate.c (the manifest.ttl reader), in a fixed order. As the Makefile does, each
# is compiled with fuzz/alloc.h forced on it, which sends the reader's malloc, calloc, realloc, strdup and
# free to fuzz/alloc.c: the count of the bytes a reader holds that the reject_clean and bounded_alloc
# properties read. The rest of the host (JACK, the CLAP and LV2 loaders) is not a target and is not built.
mkdir -p "$WORK/obj"
objs=()
for src in src/lv2_locate.c src/preset_file.c; do
  obj="$WORK/obj/$(basename "$src" .c).o"
  $CC $CFLAGS -std=gnu99 -D_GNU_SOURCE -Isrc -include fuzz/alloc.h -c "$src" -o "$obj"
  objs+=("$obj")
done
$AR rcs "$WORK/libomx-clap-readers.a" "${objs[@]}"

# The allocation count every fuzz target links, compiled once with the harness's flags.
$CC $CFLAGS -std=gnu99 -D_GNU_SOURCE -Isrc -Ifuzz -c fuzz/alloc.c -o "$WORK/alloc.o"

# The fuzz targets.
for h in state manifest; do
  $CC $CFLAGS -std=gnu99 -D_GNU_SOURCE -Isrc -Ifuzz -c "fuzz/fuzz_$h.c" -o "$WORK/fuzz_$h.o"
  $CC $CFLAGS "$WORK/fuzz_$h.o" "$WORK/alloc.o" -o "$OUT/fuzz_$h" $LIB_FUZZING_ENGINE "$WORK/libomx-clap-readers.a" -lm
done

# fuzz_preset, from $SRC/fuzz_preset/ (the Dockerfile copies them in): fuzz/fuzz_preset.c and fuzz/alloc.c, each with one
# change. alloc.c also notes when the C library's allocator returns NULL on a request of at most the call's bound, and
# fuzz_preset.c ends a call, with no abort, once memory has run out, for the reader or for the harness, so that a correct
# refusal for lack of memory is not an abort; a NULL on a request past the bound is still judged by the checks. The
# other fuzz targets keep fuzz/alloc.c as it is. fuzz_preset_oom.c tests this; it is not built here.
$CC $CFLAGS -std=gnu99 -D_GNU_SOURCE -Isrc -Ifuzz -c "$SRC/fuzz_preset/alloc.c" -o "$WORK/alloc_preset.o"
$CC $CFLAGS -std=gnu99 -D_GNU_SOURCE -Isrc -Ifuzz -c "$SRC/fuzz_preset/fuzz_preset.c" -o "$WORK/fuzz_preset.o"
$CC $CFLAGS "$WORK/fuzz_preset.o" "$WORK/alloc_preset.o" -o "$OUT/fuzz_preset" $LIB_FUZZING_ENGINE \
  "$WORK/libomx-clap-readers.a" -lm
