(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AF0l.v, with its module paths and addresses changed; 1 of its 15 lines of code is new or changed and 1 line of the source is left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x52d80;        pc_wrap_malloc := 0x52bac;   pc_malloc_ra0 := 0x52e48;
pc_free := 0x52bb0;          pc_wrap_free := 0x52ba8;     pc_free_ra0 := 0x52ce8;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3cf80 else if cid =? 3 then 0x3d0f4 else if cid =? 4 then 0x3d2a0 else 0;
pc_asan_memcpy := 0x51858;   pc_asan_memset := 0x51cf4;
pc_wrap_memcpy := 0x51854;   pc_wrap_memset := 0x51850;   pc_wrap_memcmp := 0x4219c;  pc_wrap_bcmp := 0x421a0;
pc_wrap_read := 0x421ac;     pc_wrap_fwrite := 0x421b0;   pc_wrap_vprintf := 0x421bc; pc_wrap_vfprintf := 0x421c0;
pc_wrap_fprintf := 0x421c8;  pc_wrap_memchr := 0x421a4;   pc_wrap_strnlen := 0x42190;
pc_region_is_poisoned := 0x543d4;
pc_spin_mmapdie := 0x5fc60;  pc_spin_batch := 0x3603c;    pc_spin_freearray := 0x34a18; pc_spin_shadow := 0x6e168
|}.
