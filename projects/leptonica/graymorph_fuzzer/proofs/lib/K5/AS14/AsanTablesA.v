(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x643000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3ec48; rw_lo := 0xde000; rw_len := 0x565000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x737f0; x_imemcpy := 0x73774; x_memset := 0xd874c; x_memcpy := 0xd8348; x_memiszero := 0x73d20;
     x_istrncpy := 0x73c1c; x_sealed := 0x11aa8; x_popfree := 0x453d8;
     x_sniff := 0x74e38; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xcded0; x_envscan_k := 0xcdedc; x_pnscan := 0xcdf94; x_pnscan_k := 0xcdfa0;
     stops_more := [0x4304c; 0x44670; 0x63548; 0x69da0; 0x69db4; 0x69dc8; 0x6f86c; 0x6f93c; 0x7ce68; 0x7dd74; 0x7df04; 0x7e074; 0x87c5c];
     x_hsort := 0x601cc |}.

Definition ASAN_A_TEXT_LO : Z := 0x3ec48.
Definition ASAN_A_TEXT_N : nat := 162702.
Definition ASAN_A_MAIN : Z := 0x8fe78.
Definition asan_a_init : acs := init_acs_of ASAN_A.

(* [comment removed for export] *)
