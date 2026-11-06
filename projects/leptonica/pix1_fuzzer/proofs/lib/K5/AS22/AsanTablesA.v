(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x627000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3ad58; rw_lo := 0xc5000; rw_len := 0x562000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x6f754; x_imemcpy := 0x6f6d8; x_memset := 0xbefb4; x_memcpy := 0xbebb0; x_memiszero := 0x6fc84;
     x_istrncpy := 0x6fb80; x_sealed := 0x119ef; x_popfree := 0x414e8;
     x_sniff := 0x70d9c; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xb4738; x_envscan_k := 0xb4744; x_pnscan := 0xb47fc; x_pnscan_k := 0xb4808;
     stops_more := [0x3f15c; 0x40780; 0x5f4ac; 0x65d04; 0x65d18; 0x65d2c; 0x6b7d0; 0x6b8a0; 0x78dcc; 0x79cd8; 0x79e68; 0x79fd8; 0x83bc0];
     x_hsort := 0x5c130 |}.

Definition ASAN_A_TEXT_LO : Z := 0x3ad58.
Definition ASAN_A_TEXT_N : nat := 140644.
Definition ASAN_A_MAIN : Z := 0x8bddc.
Definition asan_a_init : acs := init_acs_of ASAN_A.
