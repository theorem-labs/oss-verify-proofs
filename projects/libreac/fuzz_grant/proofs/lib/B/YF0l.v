(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v, with its module paths changed, its addresses moved to libreac/fuzz_grant's ASan build and the side-stack entries of classes 0 and 4, which fuzz_grant's program calls, added. *)
(* Modified by Theorem Labs, 2026-10: grant A's file relocated to image B (fuzz_grant.asan-ubsan fde52226dc48) by port_core 53ec3af2afc9, A -> B; the numbers below are image B's unless a comment says image A. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x530b0;        pc_wrap_malloc := 0x52edc;   pc_malloc_ra0 := 0x53178;
pc_free := 0x52ee0;          pc_wrap_free := 0x52ed8;     pc_free_ra0 := 0x53018;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3cf4c else if cid =? 1 then 0x3d0c0 else if cid =? 2 then 0x3d250 else if cid =? 4 then 0x3d3ec else if cid =? 6 then 0x3d5b8 else 0;
pc_asan_memcpy := 0x51b88;   pc_asan_memset := 0x52024;
pc_wrap_memcpy := 0x51b84;   pc_wrap_memset := 0x51b80;   pc_wrap_memcmp := 0x424cc;  pc_wrap_bcmp := 0x424d0;
pc_wrap_read := 0x424dc;     pc_wrap_fwrite := 0x424e0;   pc_wrap_vprintf := 0x424ec; pc_wrap_vfprintf := 0x424f0;
pc_wrap_fprintf := 0x424f8;  pc_wrap_memchr := 0x424d4;   pc_wrap_strnlen := 0x424c0;
pc_region_is_poisoned := 0x54704;
pc_spin_mmapdie := 0x5ff90;  pc_spin_batch := 0x36008;    pc_spin_freearray := 0x349e4; pc_spin_shadow := 0x6e498
|}.
