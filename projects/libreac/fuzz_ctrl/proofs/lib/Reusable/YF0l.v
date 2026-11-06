(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YF0l.v (origin/ossv/recipes c8557374ad2e), with its module paths changed; its code addresses moved to the same functions and offsets of fuzz_ctrl's asan-ubsan image (sha256 12136677c5cf...), pc_malloc_ra0 / pc_free_ra0 recomputed as the return of the GetCurrentPc call on the Unwind branch of the malloc / free interceptor, the rule that gives cgif's values, and pc_stack_malloc keyed by class id from the symbols __asan_stack_malloc_<cid> of that image (classes 0, 1, 2, 6; cgif has 1, 2). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x5368c;        pc_wrap_malloc := 0x534b8;   pc_malloc_ra0 := 0x53754;
pc_free := 0x534bc;          pc_wrap_free := 0x534b4;     pc_free_ra0 := 0x535f4;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3d6f4 else if cid =? 1 then 0x3d868 else if cid =? 2 then 0x3d9f8 else if cid =? 6 then 0x3db94 else 0;
pc_asan_memcpy := 0x52164;   pc_asan_memset := 0x52600;
pc_wrap_memcpy := 0x52160;   pc_wrap_memset := 0x5215c;   pc_wrap_memcmp := 0x42aa8;  pc_wrap_bcmp := 0x42aac;
pc_wrap_read := 0x42ab8;     pc_wrap_fwrite := 0x42abc;   pc_wrap_vprintf := 0x42ac8; pc_wrap_vfprintf := 0x42acc;
pc_wrap_fprintf := 0x42ad4;  pc_wrap_memchr := 0x42ab0;   pc_wrap_strnlen := 0x42a9c;
pc_region_is_poisoned := 0x54ce0;
pc_spin_mmapdie := 0x6056c;  pc_spin_batch := 0x367b0;    pc_spin_freearray := 0x3518c; pc_spin_shadow := 0x6ea74
|}.
