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

Definition ASAN_B : atable :=
  {| img_lo := 0x10000; img_hi := 0x6d6000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x5aee0; rw_lo := 0x171000; rw_len := 0x565000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x94ab8; x_imemcpy := 0x94a3c; x_memset := 0x169974; x_memcpy := 0x169570; x_memiszero := 0x95004;
     x_istrncpy := 0x94ee4; x_sealed := 0x11b83; x_popfree := 0x61590;
     x_sniff := 0x9611c; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x157a3c; x_envscan_k := 0x157a48; x_pnscan := 0x157b00; x_pnscan_k := 0x157b0c;
     stops_more := [0x5f204; 0x60828; 0x84b74; 0x8b17c; 0x8b190; 0x8b1a4; 0x90b34; 0x90c04; 0x9e14c; 0x9f058; 0x9f1e8; 0xa8f40];
     x_hsort := 0x81204 |}.

Definition ASAN_B_TEXT_LO : Z := 0x5aee0.
Definition ASAN_B_TEXT_N : nat := 283733.
Definition ASAN_B_MAIN : Z := 0xb115c.
Definition asan_b_init : acs := init_acs_of ASAN_B.
