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
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x73a000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x90368; rw_lo := 0x1c8000; rw_len := 0x572000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0xca4b4; x_imemcpy := 0xca438; x_memset := 0x1c1bfc; x_memcpy := 0x1c17c8; x_memiszero := 0xcaa00;
     x_istrncpy := 0xca8e0; x_sealed := 0x1278b; x_popfree := 0x96b04;
     x_sniff := 0xcbb18; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0x1b15a0; x_envscan_k := 0x1b15ac; x_pnscan := 0x1b1664; x_pnscan_k := 0x1b1670;
     stops_more := [0x94778; 0x95d9c; 0xba1f8; 0xc0a64; 0xc0a78; 0xc0a8c; 0xc6530; 0xc6600; 0xd3b48; 0xd4a54; 0xd4be4; 0xde93c];
     x_hsort := 0xb6b0c |}.

Definition ASAN_A_TEXT_LO : Z := 0x90368.
Definition ASAN_A_TEXT_N : nat := 318952.
Definition ASAN_A_MAIN : Z := 0xe6e04.
Definition asan_a_init : acs := init_acs_of ASAN_A.

(* [comment removed for export] *)
