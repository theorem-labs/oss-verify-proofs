(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v at 25e3d17bdb50, with its module paths changed, its addresses moved to libreac/fuzz_grant's ASan build and the side-stack entries of classes 0 and 4, which fuzz_grant's program calls, added. *)
(* Modified by Theorem Labs, 2026-10: grant A's file relocated to image B (fuzz_grant.asan-ubsan fde52226dc48) by port_core 53ec3af2afc9, A -> B; the numbers below are image B's unless a comment says image A. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/B/YF0l.v at 4f87de75d67 (donor image sha256 fde52226dc48), with its module paths changed and its addresses moved to reac-repacer/fuzz_wire's ASan+UBSan build; pc_stack_malloc keeps only classes 0 and 1, as fuzz_wire.asan-ubsan links only __asan_stack_malloc_0 and __asan_stack_malloc_1 (fuzz_grant's classes 2, 4 and 6 are removed), and pc_asan_memset is 0, as fuzz_wire.asan-ubsan links no __asan_memset. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x5226c;        pc_wrap_malloc := 0x52098;   pc_malloc_ra0 := 0x52334;
pc_free := 0x5209c;          pc_wrap_free := 0x52094;     pc_free_ra0 := 0x521d4;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3c524 else if cid =? 1 then 0x3c698 else 0;
pc_asan_memcpy := 0x50c14;   pc_asan_memset := 0;
pc_wrap_memcpy := 0x50c10;   pc_wrap_memset := 0x50c0c;   pc_wrap_memcmp := 0x41558;  pc_wrap_bcmp := 0x4155c;
pc_wrap_read := 0x41568;     pc_wrap_fwrite := 0x4156c;   pc_wrap_vprintf := 0x41578; pc_wrap_vfprintf := 0x4157c;
pc_wrap_fprintf := 0x41584;  pc_wrap_memchr := 0x41560;   pc_wrap_strnlen := 0x4154c;
pc_region_is_poisoned := 0x538c0;
pc_spin_mmapdie := 0x5f14c;  pc_spin_batch := 0x355e0;    pc_spin_freearray := 0x33fbc; pc_spin_shadow := 0x6d654
|}.
