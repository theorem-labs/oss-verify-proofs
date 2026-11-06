(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AF0l.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_scene/proofs/lib/A/AF0l.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to libdiginet/fuzz_codec's ASan build. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x52ec0;        pc_wrap_malloc := 0x52cec;   pc_malloc_ra0 := 0x52f88;
pc_free := 0x52cf0;          pc_wrap_free := 0x52ce8;     pc_free_ra0 := 0x52e28;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3d0fc else if cid =? 1 then 0x3d270 else if cid =? 3 then 0x3d400 else 0;
pc_asan_memcpy := 0x51998;   pc_asan_memset := 0x51e34;
pc_wrap_memcpy := 0x51994;   pc_wrap_memset := 0x51990;   pc_wrap_memcmp := 0x422dc;  pc_wrap_bcmp := 0x422e0;
pc_wrap_read := 0x422ec;     pc_wrap_fwrite := 0x422f0;   pc_wrap_vprintf := 0x422fc; pc_wrap_vfprintf := 0x42300;
pc_wrap_fprintf := 0x42308;  pc_wrap_memchr := 0x422e4;   pc_wrap_strnlen := 0x422d0;
pc_region_is_poisoned := 0x54514;
pc_spin_mmapdie := 0x5fda0;  pc_spin_batch := 0x361b8;    pc_spin_freearray := 0x34b94; pc_spin_shadow := 0x6e2a8
|}.
