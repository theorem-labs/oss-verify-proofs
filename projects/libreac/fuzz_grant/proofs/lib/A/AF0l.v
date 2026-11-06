(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v, with its module paths changed, its addresses moved to libreac/fuzz_grant's ASan build and the side-stack entries of classes 0 and 4, which fuzz_grant's program calls, added. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x52d24;        pc_wrap_malloc := 0x52b50;   pc_malloc_ra0 := 0x52dec;
pc_free := 0x52b54;          pc_wrap_free := 0x52b4c;     pc_free_ra0 := 0x52c8c;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3cda4 else if cid =? 1 then 0x3cf18 else if cid =? 2 then 0x3d0a8 else if cid =? 4 then 0x3d244 else 0;
pc_asan_memcpy := 0x517fc;   pc_asan_memset := 0x51c98;
pc_wrap_memcpy := 0x517f8;   pc_wrap_memset := 0x517f4;   pc_wrap_memcmp := 0x42140;  pc_wrap_bcmp := 0x42144;
pc_wrap_read := 0x42150;     pc_wrap_fwrite := 0x42154;   pc_wrap_vprintf := 0x42160; pc_wrap_vfprintf := 0x42164;
pc_wrap_fprintf := 0x4216c;  pc_wrap_memchr := 0x42148;   pc_wrap_strnlen := 0x42134;
pc_region_is_poisoned := 0x54378;
pc_spin_mmapdie := 0x5fc04;  pc_spin_batch := 0x35e60;    pc_spin_freearray := 0x3483c; pc_spin_shadow := 0x6e10c
|}.
