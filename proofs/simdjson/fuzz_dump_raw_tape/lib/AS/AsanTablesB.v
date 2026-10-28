(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

Definition ASAN_B : atable :=
  {| img_lo := 0x10000; img_hi := 0x6ce000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x583dc; rw_lo := 0x168000; rw_len := 0x566000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x92128; x_imemcpy := 0x920ac; x_memset := 0x161214; x_memcpy := 0x160e10; x_memiszero := 0x92674;
     x_istrncpy := 0x92554; x_sealed := 0x11b35; x_popfree := 0x5ea8c;
     x_sniff := 0x9378c; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x14f2dc; x_envscan_k := 0x14f2e8; x_pnscan := 0x14f3a0; x_pnscan_k := 0x14f3ac;
     stops_more := [0x5c700; 0x5dd24; 0x821e4; 0x887ec; 0x88800; 0x88814; 0x8e1a4; 0x8e274; 0x9b7bc; 0x9c6c8; 0x9c858; 0xa65b0];
     x_hsort := 0x7e874 |}.

Definition ASAN_B_TEXT_LO : Z := 0x583dc.
Definition ASAN_B_TEXT_N : nat := 277787.
Definition ASAN_B_MAIN : Z := 0xae7cc.
Definition asan_b_init : acs := init_acs_of ASAN_B.
