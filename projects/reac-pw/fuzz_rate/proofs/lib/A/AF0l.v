(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AF0l.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_rate's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x52d88;        pc_wrap_malloc := 0x52bb4;   pc_malloc_ra0 := 0x52e50;
pc_free := 0x52bb8;          pc_wrap_free := 0x52bb0;     pc_free_ra0 := 0x52cf0;
pc_stack_malloc := fun cid => if cid =? 1 then 0x3cf9c else if cid =? 2 then 0x3d12c else if cid =? 3 then 0x3d2c8 else 0;
pc_asan_memcpy := 0x51860;   pc_asan_memset := 0x51cfc;
pc_wrap_memcpy := 0x5185c;   pc_wrap_memset := 0x51858;   pc_wrap_memcmp := 0x421a4;  pc_wrap_bcmp := 0x421a8;
pc_wrap_read := 0x421b4;     pc_wrap_fwrite := 0x421b8;   pc_wrap_vprintf := 0x421c4; pc_wrap_vfprintf := 0x421c8;
pc_wrap_fprintf := 0x421d0;  pc_wrap_memchr := 0x421ac;   pc_wrap_strnlen := 0x42198;
pc_region_is_poisoned := 0x543dc;
pc_spin_mmapdie := 0x5fc68;  pc_spin_batch := 0x36058;    pc_spin_freearray := 0x34a34; pc_spin_shadow := 0x6e170
|}.
