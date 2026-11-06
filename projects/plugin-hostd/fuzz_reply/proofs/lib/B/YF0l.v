(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YF0l.v, with its module paths changed, and its fuzz_reply.asan-ubsan addresses relocated from cgif_file_fuzzer.asan-ubsan (26 numerals; per-numeral report). *)
(* Modified by Theorem Labs, 2026-10: pc_stack_malloc re-keyed to fuzz_reply.asan-ubsan's FakeStack classes: class 1 is __asan_stack_malloc_1 (0x3d334, the twin of cgif's 0x3c8d4), class 0 is __asan_stack_malloc_0 (0x3d1c0, new in fuzz_reply); fuzz_reply has no __asan_stack_malloc_2 (cgif's class 2 at 0x3ca64), as lib/A/AF0l.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x5401c;        pc_wrap_malloc := 0x53e44;   pc_malloc_ra0 := 0x540e4;
pc_free := 0x53e4c;          pc_wrap_free := 0x53e40;     pc_free_ra0 := 0x53f84;
pc_stack_malloc := fun cid => if cid =? 1 then 0x3d334 else if cid =? 0 then 0x3d1c0 else 0;
pc_asan_memcpy := 0x52780;   pc_asan_memset := 0x52c1c;
pc_wrap_memcpy := 0x5277c;   pc_wrap_memset := 0x52778;   pc_wrap_memcmp := 0x42200;  pc_wrap_bcmp := 0x42204;
pc_wrap_read := 0x42210;     pc_wrap_fwrite := 0x42218;   pc_wrap_vprintf := 0x42224; pc_wrap_vfprintf := 0x42228;
pc_wrap_fprintf := 0x42230;  pc_wrap_memchr := 0x42208;   pc_wrap_strnlen := 0x421e8;
pc_region_is_poisoned := 0x559b4;
pc_spin_mmapdie := 0x612d8;  pc_spin_batch := 0x3627c;    pc_spin_freearray := 0x34c58; pc_spin_shadow := 0x6fda0
|}.
