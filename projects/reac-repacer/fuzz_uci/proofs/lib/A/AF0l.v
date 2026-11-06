(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v, with its module paths changed, its addresses moved to libreac/fuzz_grant's ASan build and the side-stack entries of classes 0 and 4, which fuzz_grant's program calls, added. *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_grant/lib/A/AF0l.v (donor image sha256 c2c7559b29bd), with its module paths changed and its addresses moved to reac-repacer/fuzz_uci's ASan build. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x5195c;        pc_wrap_malloc := 0x51788;   pc_malloc_ra0 := 0x51a24;
pc_free := 0x5178c;          pc_wrap_free := 0x51784;     pc_free_ra0 := 0x518c4;
pc_stack_malloc := fun cid => if cid =? 1 then 0x3c1b8 else 0;
pc_asan_memcpy := 0x50674;   pc_asan_memset := 0;
pc_wrap_memcpy := 0x50670;   pc_wrap_memset := 0x5066c;   pc_wrap_memcmp := 0x41078;  pc_wrap_bcmp := 0;
pc_wrap_read := 0x41084;     pc_wrap_fwrite := 0x41088;   pc_wrap_vprintf := 0x41094; pc_wrap_vfprintf := 0x41098;
pc_wrap_fprintf := 0x410a0;  pc_wrap_memchr := 0x4107c;   pc_wrap_strnlen := 0x4106c;
pc_region_is_poisoned := 0x52fb0;
pc_spin_mmapdie := 0x5e83c;  pc_spin_batch := 0x35274;    pc_spin_freearray := 0x33c50; pc_spin_shadow := 0x6cd44
|}.
