(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x79a000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x9ff5c; rw_lo := 0x21f000; rw_len := 0x57b000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0xdd11c; x_imemcpy := 0xdd0a0; x_memset := 0x218338; x_memcpy := 0x217f04; x_memiszero := 0xdd668;
     x_istrncpy := 0xdd548; x_sealed := 0x12af6; x_popfree := 0xa66f8;
     x_sniff := 0xde780; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0x206a94; x_envscan_k := 0x206aa0; x_pnscan := 0x206b58; x_pnscan_k := 0x206b64;
     stops_more := [0xa436c; 0xa5990; 0xcce60; 0xd36cc; 0xd36e0; 0xd36f4; 0xd9198; 0xd9268; 0xe67dc; 0xe7714; 0xe78a4; 0xf162c];
     x_hsort := 0xc9774 |}.

Definition ASAN_A_TEXT_LO : Z := 0x9ff5c.
Definition ASAN_A_TEXT_N : nat := 391474.
Definition ASAN_A_MAIN : Z := 0xf9b08.
Definition asan_a_init : acs := init_acs_of ASAN_A.
