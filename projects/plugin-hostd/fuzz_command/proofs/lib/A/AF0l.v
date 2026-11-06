(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v, with its module paths changed, its addresses moved to plugin-hostd/fuzz_command's ASan build, and pc_stack_malloc keyed by fuzz_command's side-stack classes 0, 1, 3, 4, 5, 7 (cgif's class 2 has no counterpart). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x58b58;        pc_wrap_malloc := 0x58984;   pc_malloc_ra0 := 0x58c20;
pc_free := 0x58988;          pc_wrap_free := 0x58980;     pc_free_ra0 := 0x58ac0;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3f908 else if cid =? 1 then 0x3fa7c else if cid =? 3 then 0x3fc0c
else if cid =? 4 then 0x3fdb8 else if cid =? 5 then 0x3ff84 else if cid =? 7 then 0x40244 else 0;
pc_asan_memcpy := 0x57630;   pc_asan_memset := 0x57acc;
pc_wrap_memcpy := 0x5762c;   pc_wrap_memset := 0x57628;   pc_wrap_memcmp := 0x45150;  pc_wrap_bcmp := 0x45154;
pc_wrap_read := 0x45160;     pc_wrap_fwrite := 0x45164;   pc_wrap_vprintf := 0x45170; pc_wrap_vfprintf := 0x45174;
pc_wrap_fprintf := 0x4517c;  pc_wrap_memchr := 0x45158;   pc_wrap_strnlen := 0x45134;
pc_region_is_poisoned := 0x5a1ac;
pc_spin_mmapdie := 0x65a38;  pc_spin_batch := 0x389c4;    pc_spin_freearray := 0x373a0; pc_spin_shadow := 0x73f40
|}.
