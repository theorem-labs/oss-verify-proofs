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
  {| img_lo := 0x10000; img_hi := 0x628000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3af08; rw_lo := 0xc5000; rw_len := 0x563000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x6f904; x_imemcpy := 0x6f888; x_memset := 0xbf8b0; x_memcpy := 0xbf4ac; x_memiszero := 0x6fe34;
     x_istrncpy := 0x6fd30; x_sealed := 0x11a04; x_popfree := 0x41698;
     x_sniff := 0x70f4c; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xb5034; x_envscan_k := 0xb5040; x_pnscan := 0xb50f8; x_pnscan_k := 0xb5104;
     stops_more := [0x3f30c; 0x40930; 0x5f65c; 0x65eb4; 0x65ec8; 0x65edc; 0x6b980; 0x6ba50; 0x78f7c; 0x79e88; 0x7a018; 0x7a188; 0x83d70];
     x_hsort := 0x5c2e0 |}.

Definition ASAN_A_TEXT_LO : Z := 0x3af08.
Definition ASAN_A_TEXT_N : nat := 141111.
Definition ASAN_A_MAIN : Z := 0x8bf8c.
Definition asan_a_init : acs := init_acs_of ASAN_A.
