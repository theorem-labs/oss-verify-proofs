(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v, with its module paths changed, and its fuzz_reply.asan addresses relocated from cgif_file_fuzzer.asan (25 numerals; per-numeral report). *)
(* Modified by Theorem Labs, 2026-10: pc_stack_malloc re-keyed to fuzz_reply.asan's FakeStack classes: class 1 is __asan_stack_malloc_1 (0x3d2dc, the twin of cgif's 0x3c8a4), class 0 is __asan_stack_malloc_0 (0x3d168, new in fuzz_reply); fuzz_reply has no __asan_stack_malloc_2 (cgif's class 2 at 0x3ca34). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x53fc4;        pc_wrap_malloc := 0x53dec;   pc_malloc_ra0 := 0x5408c;
pc_free := 0x53df4;          pc_wrap_free := 0x53de8;     pc_free_ra0 := 0x53f2c;
pc_stack_malloc := fun cid => if cid =? 1 then 0x3d2dc else if cid =? 0 then 0x3d168 else 0;
pc_asan_memcpy := 0x52728;   pc_asan_memset := 0x52bc4;
pc_wrap_memcpy := 0x52724;   pc_wrap_memset := 0x52720;   pc_wrap_memcmp := 0x421a8;  pc_wrap_bcmp := 0x421ac;
pc_wrap_read := 0x421b8;     pc_wrap_fwrite := 0x421c0;   pc_wrap_vprintf := 0x421cc; pc_wrap_vfprintf := 0x421d0;
pc_wrap_fprintf := 0x421d8;  pc_wrap_memchr := 0x421b0;   pc_wrap_strnlen := 0x42190;
pc_region_is_poisoned := 0x5595c;
pc_spin_mmapdie := 0x61280;  pc_spin_batch := 0x36224;    pc_spin_freearray := 0x34c00; pc_spin_shadow := 0x6fd48
|}.
