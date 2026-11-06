#!/bin/bash -eu
# Copyright 2026 Pau Aliagas <linuxnow@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Builds reac-repacer's four fuzz targets (fuzz/fuzz_*.c in the reac-repacer repository) into $OUT.
# reac-repacer's own Makefile builds them with a native clang and libFuzzer; this script makes the same harnesses into
# static riscv64 programs, each linked against a static library of the readers of this build and one of libreac.
flags=(-std=c11 -D_DEFAULT_SOURCE -Iinclude -Ifuzz -I"$SRC/libreac/include")
mkdir -p "$WORK/obj"

# libreac: src/reac.c, the one file of it the readers call into (reac_frame_clean_len, reac_frame_is_reac), laid
# out in $SRC/libreac by the Dockerfile.
$CC $CFLAGS "${flags[@]}" -c "$SRC/libreac/src/reac.c" -o "$WORK/obj/reac.o"
$AR rcs "$WORK/libreac.a" "$WORK/obj/reac.o"

# The library: the daemon's readers of wire and config bytes, src/repace_wire.c (the frame readers and the emit
# rewrite) and src/repace_conf.c (the warm-start lock, the uci reply and the hot-parameter ranges), in a fixed order.
# The rest of the daemon (tools/reac_repacer.c: the sockets, the threads, the pacing clock) is not a target and is not
# built.
objs=()
for src in src/repace_wire.c src/repace_conf.c; do
  obj="$WORK/obj/$(basename "$src" .c).o"
  $CC $CFLAGS "${flags[@]}" -c "$src" -o "$obj"
  objs+=("$obj")
done
$AR rcs "$WORK/librepace.a" "${objs[@]}"

# The fuzz targets.
for h in wire egress lock uci; do
  $CC $CFLAGS "${flags[@]}" -c "fuzz/fuzz_$h.c" -o "$WORK/fuzz_$h.o"
  $CC $CFLAGS "$WORK/fuzz_$h.o" -o "$OUT/fuzz_$h" $LIB_FUZZING_ENGINE "$WORK/librepace.a" "$WORK/libreac.a"
done
