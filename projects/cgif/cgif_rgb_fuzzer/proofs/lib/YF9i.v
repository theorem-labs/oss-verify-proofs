(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0h.
Local Open Scope Z_scope.
Definition Trb_code : acode := {|
pc_malloc := 0x535a0;        pc_wrap_malloc := 0x533c8;   pc_malloc_ra0 := 0x53668;
pc_free := 0x533d0;          pc_wrap_free := 0x533c4;     pc_free_ra0 := 0x53508;
pc_stack_malloc := fun cid => if cid =? 1 then 0x3d170 else if cid =? 2 then 0x3d300 else 0;
pc_asan_memcpy := 0x52074;   pc_asan_memset := 0x52510;
pc_wrap_memcpy := 0x52070;   pc_wrap_memset := 0x5206c;   pc_wrap_memcmp := 0x42398;  pc_wrap_bcmp := 0x4239c;
pc_wrap_read := 0x423a8;     pc_wrap_fwrite := 0x423ac;   pc_wrap_vprintf := 0x423b8; pc_wrap_vfprintf := 0x423bc;
pc_wrap_fprintf := 0x423c4;  pc_wrap_memchr := 0x423a0;   pc_wrap_strnlen := 0x4238c;
pc_region_is_poisoned := 0x54f38;
pc_spin_mmapdie := 0x607c4;  pc_spin_batch := 0x360b8;    pc_spin_freearray := 0x34a94; pc_spin_shadow := 0x6eccc
|}.
