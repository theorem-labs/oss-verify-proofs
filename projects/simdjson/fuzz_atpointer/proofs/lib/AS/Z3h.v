(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z78 Z2z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

Definition ASAN_B : atable :=
  {| img_lo := 0x10000; img_hi := 0x676000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x447c4; rw_lo := 0x114000; rw_len := 0x562000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x79f88; x_imemcpy := 0x79f0c; x_memset := 0x10dd6c; x_memcpy := 0x10d968; x_memiszero := 0x7a4b8;
     x_istrncpy := 0x7a3b4; x_sealed := 0x11a8f; x_popfree := 0x4ae74;
     x_sniff := 0x7b5d0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0xfecc0; x_envscan_k := 0xfeccc; x_pnscan := 0xfed84; x_pnscan_k := 0xfed90;
     stops_more := [0x48ae8; 0x4a10c; 0x69b04; 0x7064c; 0x70660; 0x70674; 0x76004; 0x760d4; 0x83600; 0x8450c; 0x8469c; 0x8e3f4];
     x_hsort := 0x66194 |}.

Definition ASAN_B_TEXT_LO : Z := 0x447c4.
Definition ASAN_B_TEXT_N : nat := 211569.
Definition ASAN_B_MAIN : Z := 0x96610.
Definition asan_b_init : acs := init_acs_of ASAN_B.
