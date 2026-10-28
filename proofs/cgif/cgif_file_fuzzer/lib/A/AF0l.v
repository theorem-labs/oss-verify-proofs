(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x52b04;        pc_wrap_malloc := 0x52930;   pc_malloc_ra0 := 0x52bcc;
pc_free := 0x52934;          pc_wrap_free := 0x5292c;     pc_free_ra0 := 0x52a6c;
pc_stack_malloc := fun cid => if cid =? 1 then 0x3c8a4 else if cid =? 2 then 0x3ca34 else 0;
pc_asan_memcpy := 0x515dc;   pc_asan_memset := 0x51a78;
pc_wrap_memcpy := 0x515d8;   pc_wrap_memset := 0x515d4;   pc_wrap_memcmp := 0x41900;  pc_wrap_bcmp := 0x41904;
pc_wrap_read := 0x41910;     pc_wrap_fwrite := 0x41914;   pc_wrap_vprintf := 0x41920; pc_wrap_vfprintf := 0x41924;
pc_wrap_fprintf := 0x4192c;  pc_wrap_memchr := 0x41908;   pc_wrap_strnlen := 0x418f4;
pc_region_is_poisoned := 0x54158;
pc_spin_mmapdie := 0x5f9e4;  pc_spin_batch := 0x35960;    pc_spin_freearray := 0x3433c; pc_spin_shadow := 0x6deec
|}.
