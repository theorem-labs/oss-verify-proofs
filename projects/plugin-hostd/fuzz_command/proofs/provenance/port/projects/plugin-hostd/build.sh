#!/bin/bash -eu
# Copyright 2026 Pau Aliagas <linuxnow@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Builds plugin-hostd's two fuzz targets (fuzz/fuzz_*.c in the plugin-hostd repository) into $OUT.
# plugin-hostd's own Makefile builds them with a native clang and libFuzzer; this script makes the same harnesses into
# static riscv64 programs. The harnesses read mod-host's protocol headers, laid out in $SRC/mod-host by the Dockerfile.
flags=(-std=c11 -D_GNU_SOURCE -Iinclude -Isrc -Ifuzz -I"$SRC/mod-host/src")

# The library: the daemon's command parser and dispatcher, src/verbs.c, the code fuzz_command drives.
mkdir -p "$WORK/obj"
$CC $CFLAGS "${flags[@]}" -c src/verbs.c -o "$WORK/obj/verbs.o"
$AR rcs "$WORK/libplugin-hostd.a" "$WORK/obj/verbs.o"

# fuzz_command: the library, with everything below it (the supervisor, the pins, the descriptors, the socket's send)
# answered by the harness's recorder, fuzz/recorder.c.
$CC $CFLAGS "${flags[@]}" -c fuzz/fuzz_command.c -o "$WORK/fuzz_command.o"
$CC $CFLAGS "${flags[@]}" -c fuzz/recorder.c -o "$WORK/recorder.o"
$CC $CFLAGS "$WORK/fuzz_command.o" "$WORK/recorder.o" -o "$OUT/fuzz_command" $LIB_FUZZING_ENGINE \
  "$WORK/libplugin-hostd.a"

# fuzz_reply: the relay of the workers' feedback, src/relay.c. The harness includes the file itself, with its socket
# calls renamed to the harness's own and a line limit of 6000 bytes, as plugin-hostd's Makefile builds it; so the
# relay is compiled into the harness's object, and no library object is linked for it.
$CC $CFLAGS "${flags[@]}" -c fuzz/fuzz_reply.c -o "$WORK/fuzz_reply.o"
$CC $CFLAGS "$WORK/fuzz_reply.o" -o "$OUT/fuzz_reply" $LIB_FUZZING_ENGINE
