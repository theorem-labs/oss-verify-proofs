(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AF0l.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_scene/proofs/lib/A/AF0l.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to libdiginet/fuzz_codec's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AF0l.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from libdiginet/fuzz_codec's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AF0l.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x53010;        pc_wrap_malloc := 0x52e3c;   pc_malloc_ra0 := 0x530d8;
pc_free := 0x52e40;          pc_wrap_free := 0x52e38;     pc_free_ra0 := 0x52f78;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3d24c else if cid =? 1 then 0x3d3c0 else if cid =? 3 then 0x3d550 else 0;
pc_asan_memcpy := 0x51ae8;   pc_asan_memset := 0x51f84;
pc_wrap_memcpy := 0x51ae4;   pc_wrap_memset := 0x51ae0;   pc_wrap_memcmp := 0x4242c;  pc_wrap_bcmp := 0x42430;
pc_wrap_read := 0x4243c;     pc_wrap_fwrite := 0x42440;   pc_wrap_vprintf := 0x4244c; pc_wrap_vfprintf := 0x42450;
pc_wrap_fprintf := 0x42458;  pc_wrap_memchr := 0x42434;   pc_wrap_strnlen := 0x42420;
pc_region_is_poisoned := 0x54664;
pc_spin_mmapdie := 0x5fef0;  pc_spin_batch := 0x36308;    pc_spin_freearray := 0x34ce4; pc_spin_shadow := 0x6e3f8
|}.
