(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v, with its module paths changed, its addresses moved to plugin-hostd/fuzz_command's ASan build, and pc_stack_malloc keyed by fuzz_command's side-stack classes 0, 1, 3, 4, 5, 7 (cgif's class 2 has no counterpart). *)
(* Modified by Theorem Labs, 2026-10: copied from this harness's lib/A/AF0l.v (the twin of cgif_file_fuzzer's lib/YF0l.v), with its module paths changed (lib/A to lib/B, image Asan to AsanUbsan) and its addresses moved to plugin-hostd/fuzz_command's ASan+UBSan build. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x58ba4;        pc_wrap_malloc := 0x589d0;   pc_malloc_ra0 := 0x58c6c;
pc_free := 0x589d4;          pc_wrap_free := 0x589cc;     pc_free_ra0 := 0x58b0c;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3f954 else if cid =? 1 then 0x3fac8 else if cid =? 3 then 0x3fc58
else if cid =? 4 then 0x3fe04 else if cid =? 5 then 0x3ffd0 else if cid =? 7 then 0x40290 else 0;
pc_asan_memcpy := 0x5767c;   pc_asan_memset := 0x57b18;
pc_wrap_memcpy := 0x57678;   pc_wrap_memset := 0x57674;   pc_wrap_memcmp := 0x4519c;  pc_wrap_bcmp := 0x451a0;
pc_wrap_read := 0x451ac;     pc_wrap_fwrite := 0x451b0;   pc_wrap_vprintf := 0x451bc; pc_wrap_vfprintf := 0x451c0;
pc_wrap_fprintf := 0x451c8;  pc_wrap_memchr := 0x451a4;   pc_wrap_strnlen := 0x45180;
pc_region_is_poisoned := 0x5a1f8;
pc_spin_mmapdie := 0x65a84;  pc_spin_batch := 0x38a10;    pc_spin_freearray := 0x373ec; pc_spin_shadow := 0x73f8c
|}.
