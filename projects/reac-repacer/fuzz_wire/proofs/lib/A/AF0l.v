(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v at 25e3d17bdb50, with its module paths changed, its addresses moved to libreac/fuzz_grant's ASan build and the side-stack entries of classes 0 and 4, which fuzz_grant's program calls, added. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/AF0l.v (donor image sha256 c2c7559b29bd), with its module paths changed and its addresses moved to reac-repacer/fuzz_wire's ASan build; pc_stack_malloc keeps only classes 0 and 1, as fuzz_wire.asan holds only __asan_stack_malloc_0 and __asan_stack_malloc_1 (fuzz_grant's classes 2 and 4 are removed). *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x524cc;        pc_wrap_malloc := 0x522f8;   pc_malloc_ra0 := 0x52594;
pc_free := 0x522fc;          pc_wrap_free := 0x522f4;     pc_free_ra0 := 0x52434;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3c544 else if cid =? 1 then 0x3c6b8 else 0;
pc_asan_memcpy := 0x50c34;   pc_asan_memset := 0x510d0;
pc_wrap_memcpy := 0x50c30;   pc_wrap_memset := 0x50c2c;   pc_wrap_memcmp := 0x41578;  pc_wrap_bcmp := 0x4157c;
pc_wrap_read := 0x41588;     pc_wrap_fwrite := 0x4158c;   pc_wrap_vprintf := 0x41598; pc_wrap_vfprintf := 0x4159c;
pc_wrap_fprintf := 0x415a4;  pc_wrap_memchr := 0x41580;   pc_wrap_strnlen := 0x4156c;
pc_region_is_poisoned := 0x53b20;
pc_spin_mmapdie := 0x5f3ac;  pc_spin_batch := 0x35600;    pc_spin_freearray := 0x33fdc; pc_spin_shadow := 0x6d8b4
|}.
