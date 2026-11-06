(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x662000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x44af0; rw_lo := 0xfa000; rw_len := 0x568000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x79834; x_imemcpy := 0x797b8; x_memset := 0xf424c; x_memcpy := 0xf3e48; x_memiszero := 0x79d64;
     x_istrncpy := 0x79c60; x_sealed := 0x11be6; x_popfree := 0x4b280;
     x_sniff := 0x7ae7c; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xe98b8; x_envscan_k := 0xe98c4; x_pnscan := 0xe997c; x_pnscan_k := 0xe9988;
     stops_more := [0x48ef4; 0x4a518; 0x6958c; 0x6fde4; 0x6fdf8; 0x6fe0c; 0x758b0; 0x75980; 0x82eac; 0x83db8; 0x83f48; 0x8dca0];
     x_hsort := 0x66210 |}.

Definition ASAN_A_TEXT_LO : Z := 0x44af0.
Definition ASAN_A_TEXT_N : nat := 184996.
Definition ASAN_A_MAIN : Z := 0x95ebc.
Definition asan_a_init : acs := init_acs_of ASAN_A.
