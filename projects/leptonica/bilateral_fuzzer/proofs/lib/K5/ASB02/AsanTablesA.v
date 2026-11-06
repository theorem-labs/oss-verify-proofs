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
  {| img_lo := 0x10000; img_hi := 0x66f000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x44ca8; rw_lo := 0x107000; rw_len := 0x568000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x799ec; x_imemcpy := 0x79970; x_memset := 0x1012a0; x_memcpy := 0x100e9c; x_memiszero := 0x79f1c;
     x_istrncpy := 0x79e18; x_sealed := 0x11c06; x_popfree := 0x4b438;
     x_sniff := 0x7b034; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xf690c; x_envscan_k := 0xf6918; x_pnscan := 0xf69d0; x_pnscan_k := 0xf69dc;
     stops_more := [0x490ac; 0x4a6d0; 0x69744; 0x6ff9c; 0x6ffb0; 0x6ffc4; 0x75a68; 0x75b38; 0x83064; 0x83f70; 0x84100; 0x8de58];
     x_hsort := 0x663c8 |}.

Definition ASAN_A_TEXT_LO : Z := 0x44ca8.
Definition ASAN_A_TEXT_N : nat := 198219.
Definition ASAN_A_MAIN : Z := 0x96074.
Definition asan_a_init : acs := init_acs_of ASAN_A.
