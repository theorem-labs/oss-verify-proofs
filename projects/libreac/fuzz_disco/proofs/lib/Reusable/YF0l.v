(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Generated for fuzz_disco's asan-ubsan image. Every pc below is the donor's value carried through a Theorem Labs lane's
   resolve_code.py function pairing and checked to land at the same offset inside the paired function; the
   fake-stack entries are disco's own symbols, one per class, since disco has six allocators where the donor has
   two (a Theorem Labs lane, 2026-10-28 20:25Z). The class-6 release is stated at an explicit entry (S4's SF6_ENTRY = YB1w's
   tfib_A___asan_stack_free_6), not through acode (two Theorem Labs lanes 23:51Z). *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0f.
Import ListNotations.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x53630;        pc_wrap_malloc := 0x5345c;   pc_malloc_ra0 := 0x536f8;
pc_free := 0x53460;          pc_wrap_free := 0x53458;     pc_free_ra0 := 0x53598;
pc_stack_malloc := fun cid => if cid =? 0 then 0x3d4ec else if cid =? 1 then 0x3d660
                              else if cid =? 2 then 0x3d7f0 else if cid =? 3 then 0x3d98c
                              else if cid =? 6 then 0x3db38 else 0;
pc_asan_memcpy := 0x52108;   pc_asan_memset := 0x525a4;
pc_wrap_memcpy := 0x52104;   pc_wrap_memset := 0x52100;   pc_wrap_memcmp := 0x42a4c;  pc_wrap_bcmp := 0x42a50;
pc_wrap_read := 0x42a5c;     pc_wrap_fwrite := 0x42a60;   pc_wrap_vprintf := 0x42a6c; pc_wrap_vfprintf := 0x42a70;
pc_wrap_fprintf := 0x42a78;  pc_wrap_memchr := 0x42a54;   pc_wrap_strnlen := 0x42a40;
pc_region_is_poisoned := 0x54c84;
pc_spin_mmapdie := 0x60510;  pc_spin_batch := 0x365a8;    pc_spin_freearray := 0x34f84; pc_spin_shadow := 0x6ea18
|}.
