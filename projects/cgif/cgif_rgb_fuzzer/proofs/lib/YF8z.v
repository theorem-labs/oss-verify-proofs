(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0h.
Local Open Scope Z_scope.
Definition Tra_code : acode := {|
pc_malloc := 0x532dc;        pc_wrap_malloc := 0x53104;   pc_malloc_ra0 := 0x533a4;
pc_free := 0x5310c;          pc_wrap_free := 0x53100;     pc_free_ra0 := 0x53244;
pc_stack_malloc := fun cid => if cid =? 1 then 0x3ceac else if cid =? 2 then 0x3d03c else 0;
pc_asan_memcpy := 0x51db0;   pc_asan_memset := 0x5224c;
pc_wrap_memcpy := 0x51dac;   pc_wrap_memset := 0x51da8;   pc_wrap_memcmp := 0x420d4;  pc_wrap_bcmp := 0x420d8;
pc_wrap_read := 0x420e4;     pc_wrap_fwrite := 0x420e8;   pc_wrap_vprintf := 0x420f4; pc_wrap_vfprintf := 0x420f8;
pc_wrap_fprintf := 0x42100;  pc_wrap_memchr := 0x420dc;   pc_wrap_strnlen := 0x420c8;
pc_region_is_poisoned := 0x54c74;
pc_spin_mmapdie := 0x60500;  pc_spin_batch := 0x35f68;    pc_spin_freearray := 0x34944; pc_spin_shadow := 0x6ea08
|}.
