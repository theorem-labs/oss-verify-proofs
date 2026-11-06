(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x6c9000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x5aed0; rw_lo := 0x163000; rw_len := 0x566000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x94aa8; x_imemcpy := 0x94a2c; x_memset := 0x15c758; x_memcpy := 0x15c354; x_memiszero := 0x94ff4;
     x_istrncpy := 0x94ed4; x_sealed := 0x11b6e; x_popfree := 0x61580;
     x_sniff := 0x9610c; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x14a820; x_envscan_k := 0x14a82c; x_pnscan := 0x14a8e4; x_pnscan_k := 0x14a8f0;
     stops_more := [0x5f1f4; 0x60818; 0x84b64; 0x8b16c; 0x8b180; 0x8b194; 0x90b24; 0x90bf4; 0x9e13c; 0x9f048; 0x9f1d8; 0xa8f30];
     x_hsort := 0x811f4 |}.

Definition ASAN_A_TEXT_LO : Z := 0x5aed0.
Definition ASAN_A_TEXT_N : nat := 270255.
Definition ASAN_A_MAIN : Z := 0xb114c.
Definition asan_a_init : acs := init_acs_of ASAN_A.
