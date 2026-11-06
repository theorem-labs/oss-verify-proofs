(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x52b34;        pc_wrap_malloc := 0x52960;   pc_malloc_ra0 := 0x52bfc;
pc_free := 0x52964;          pc_wrap_free := 0x5295c;     pc_free_ra0 := 0x52a9c;
pc_stack_malloc := fun cid => if cid =? 1 then 0x3c8d4 else if cid =? 2 then 0x3ca64 else 0;
pc_asan_memcpy := 0x5160c;   pc_asan_memset := 0x51aa8;
pc_wrap_memcpy := 0x51608;   pc_wrap_memset := 0x51604;   pc_wrap_memcmp := 0x41930;  pc_wrap_bcmp := 0x41934;
pc_wrap_read := 0x41940;     pc_wrap_fwrite := 0x41944;   pc_wrap_vprintf := 0x41950; pc_wrap_vfprintf := 0x41954;
pc_wrap_fprintf := 0x4195c;  pc_wrap_memchr := 0x41938;   pc_wrap_strnlen := 0x41924;
pc_region_is_poisoned := 0x54188;
pc_spin_mmapdie := 0x5fa14;  pc_spin_batch := 0x35990;    pc_spin_freearray := 0x3436c; pc_spin_shadow := 0x6df1c
|}.
