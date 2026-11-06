(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v (origin/ossv/recipes c8557374ad2e), with its module paths changed; its code addresses moved to the same functions and offsets of fuzz_ctrl's asan image (sha256 aac16e1fe728...), pc_malloc_ra0 / pc_free_ra0 recomputed as the return of the GetCurrentPc call on the Unwind branch of the malloc / free interceptor, the rule that gives cgif's values, and pc_stack_malloc keyed by class id from the symbols __asan_stack_malloc_<cid> of that image (classes 0, 1, 2, 6; cgif has 1, 2). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x53550;        pc_wrap_malloc := 0x5337c;   pc_malloc_ra0 := 0x53618;
pc_free := 0x53380;          pc_wrap_free := 0x53378;     pc_free_ra0 := 0x534b8;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3d5b8 else if cid =? 1 then 0x3d72c else if cid =? 2 then 0x3d8bc else if cid =? 6 then 0x3da58 else 0;
pc_asan_memcpy := 0x52028;   pc_asan_memset := 0x524c4;
pc_wrap_memcpy := 0x52024;   pc_wrap_memset := 0x52020;   pc_wrap_memcmp := 0x4296c;  pc_wrap_bcmp := 0x42970;
pc_wrap_read := 0x4297c;     pc_wrap_fwrite := 0x42980;   pc_wrap_vprintf := 0x4298c; pc_wrap_vfprintf := 0x42990;
pc_wrap_fprintf := 0x42998;  pc_wrap_memchr := 0x42974;   pc_wrap_strnlen := 0x42960;
pc_region_is_poisoned := 0x54ba4;
pc_spin_mmapdie := 0x60430;  pc_spin_batch := 0x36674;    pc_spin_freearray := 0x35050; pc_spin_shadow := 0x6e938
|}.
