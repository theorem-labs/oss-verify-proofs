#!/bin/bash -eu
# Copyright 2026 Pau Aliagas <linuxnow@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Builds reac-pw's seven fuzz targets (fuzz/fuzz_*.c in the reac-pw repository) into $OUT.
# reac-pw's own fuzz/build.sh builds them with a native clang and libFuzzer; this script makes
# the same harnesses into static riscv64 programs, each linked against a static library of the
# readers of this build. No fuzz target links libreac: they use its headers and SPA's, from the
# sources file, and the box-model table of fuzz/catalogue.c. Since 1.0.42 the qdisc dump and
# the topology tap are libreac-transport's (fuzzed in libreac); fuzz_qdisc fakes the four
# reac_etf_qdisc_* calls src/reac_qdisc.c makes, so nothing here renames its socket calls.

INC=(-Isrc -Ifacts -Ifuzz -I"$SRC/libreac/include" -I"$SRC/pipewire/spa/include")
# as meson compiles reac-pw (C11, _GNU_SOURCE), with the flags of libspa-0.2.pc
STD=(-std=c11 -D_GNU_SOURCE -D_REENTRANT -fno-strict-aliasing)
# The one reader of rtnetlink replies left, compiled with its socket calls renamed to the fake
# kernel of fuzz/netlink.h, as fuzz/build.sh compiles it: the rename at the compile is the
# way docs/build-contract.md gives for functions the AddressSanitizer runtime wraps.
NET=(-U_FORTIFY_SOURCE -Dsocket=fuzz_socket -Dsend=fuzz_send -Drecv=fuzz_recv -Dclose=fuzz_close
     -Dif_nametoindex=fuzz_if_nametoindex)

# The library: the readers the fuzz targets drive, and the box-model table, in a fixed order.
mkdir -p "$WORK/obj"
objs=()
for src in src/reac_segconf.c src/reac_declared_vlan.c src/reac_box_pin.c src/reac_headamp_prop.c \
           src/reac_rate_cfg.c src/reac_role_cfg.c src/reac_qdisc.c src/reac_link_alias.c \
           src/reac_served_mark.c fuzz/catalogue.c; do
  extra=()
  case $src in
  src/reac_link_alias.c) extra=("${NET[@]}") ;;
  esac
  obj="$WORK/obj/$(basename "$src" .c).o"
  $CC $CFLAGS "${STD[@]}" "${INC[@]}" "${extra[@]}" -c "$src" -o "$obj"
  objs+=("$obj")
done
$AR rcs "$WORK/libreac-pw-readers.a" "${objs[@]}"

# The fuzz targets. Every symbol resolves inside the library and the harness: the knock takes
# no plan since 1.0.41, so reac_segconf.c refuses a `knock =` line without reading a plan table.
for h in segconf pin headamp rate role qdisc link; do
  $CC $CFLAGS "${STD[@]}" "${INC[@]}" -c "fuzz/fuzz_$h.c" -o "$WORK/fuzz_$h.o"
  $CC $CFLAGS "$WORK/fuzz_$h.o" -o "$OUT/fuzz_$h" $LIB_FUZZING_ENGINE "$WORK/libreac-pw-readers.a" -lm
done
