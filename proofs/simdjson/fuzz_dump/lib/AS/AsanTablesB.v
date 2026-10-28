(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

Definition ASAN_B : atable :=
  {| img_lo := 0x10000; img_hi := 0x6cd000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x57d90; rw_lo := 0x168000; rw_len := 0x565000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x91b04; x_imemcpy := 0x91a88; x_memset := 0x160c88; x_memcpy := 0x160884; x_memiszero := 0x92050;
     x_istrncpy := 0x91f30; x_sealed := 0x11b2c; x_popfree := 0x5e440;
     x_sniff := 0x93168; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x14ed50; x_envscan_k := 0x14ed5c; x_pnscan := 0x14ee14; x_pnscan_k := 0x14ee20;
     stops_more := [0x5c0b4; 0x5d6d8; 0x81bc0; 0x881c8; 0x881dc; 0x881f0; 0x8db80; 0x8dc50; 0x9b198; 0x9c0a4; 0x9c234; 0xa5f8c];
     x_hsort := 0x7e250 |}.

Definition ASAN_B_TEXT_LO : Z := 0x57d90.
Definition ASAN_B_TEXT_N : nat := 277835.
Definition ASAN_B_MAIN : Z := 0xae1a8.
Definition asan_b_init : acs := init_acs_of ASAN_B.
