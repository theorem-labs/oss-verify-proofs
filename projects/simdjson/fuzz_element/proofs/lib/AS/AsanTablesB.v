(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

Definition ASAN_B : atable :=
  {| img_lo := 0x10000; img_hi := 0x6d9000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x5aad4; rw_lo := 0x172000; rw_len := 0x567000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x95174; x_imemcpy := 0x950f8; x_memset := 0x16b4b4; x_memcpy := 0x16b0b0; x_memiszero := 0x956c0;
     x_istrncpy := 0x955a0; x_sealed := 0x11b74; x_popfree := 0x61184;
     x_sniff := 0x967d8; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x15957c; x_envscan_k := 0x159588; x_pnscan := 0x159640; x_pnscan_k := 0x15964c;
     stops_more := [0x5edf8; 0x6041c; 0x84cf0; 0x8b838; 0x8b84c; 0x8b860; 0x911f0; 0x912c0; 0x9e808; 0x9f714; 0x9f8a4; 0xa95fc];
     x_hsort := 0x81380 |}.

Definition ASAN_B_TEXT_LO : Z := 0x5aad4.
Definition ASAN_B_TEXT_N : nat := 285785.
Definition ASAN_B_MAIN : Z := 0xb1818.
Definition asan_b_init : acs := init_acs_of ASAN_B.
