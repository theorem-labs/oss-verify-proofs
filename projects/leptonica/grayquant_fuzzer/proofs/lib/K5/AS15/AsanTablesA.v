(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x644000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3efbc; rw_lo := 0xe0000; rw_len := 0x564000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x73d00; x_imemcpy := 0x73c84; x_memset := 0xd9cec; x_memcpy := 0xd98e8; x_memiszero := 0x74230;
     x_istrncpy := 0x7412c; x_sealed := 0x11b1b; x_popfree := 0x4574c;
     x_sniff := 0x75348; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xcccb0; x_envscan_k := 0xcccbc; x_pnscan := 0xccd74; x_pnscan_k := 0xccd80;
     stops_more := [0x433c0; 0x449e4; 0x63a58; 0x6a2b0; 0x6a2c4; 0x6a2d8; 0x6fd7c; 0x6fe4c; 0x7d378; 0x7e284; 0x7e414; 0x8816c];
     x_hsort := 0x606dc |}.

Definition ASAN_A_TEXT_LO : Z := 0x3efbc.
Definition ASAN_A_TEXT_N : nat := 163865.
Definition ASAN_A_MAIN : Z := 0x90388.
Definition asan_a_init : acs := init_acs_of ASAN_A.

(* [comment removed for export] *)
