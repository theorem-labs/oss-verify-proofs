(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

Definition ASAN_B : atable :=
  {| img_lo := 0x10000; img_hi := 0x6e0000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x5dc34; rw_lo := 0x179000; rw_len := 0x567000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x97ef4; x_imemcpy := 0x97e78; x_memset := 0x1721b4; x_memcpy := 0x171db0; x_memiszero := 0x98440;
     x_istrncpy := 0x98320; x_sealed := 0x11baa; x_popfree := 0x642f0;
     x_sniff := 0x99558; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x15fcac; x_envscan_k := 0x15fcb8; x_pnscan := 0x15fd70; x_pnscan_k := 0x15fd7c;
     stops_more := [0x61f64; 0x63588; 0x87a70; 0x8e5b8; 0x8e5cc; 0x8e5e0; 0x93f70; 0x94040; 0xa1588; 0xa2494; 0xa2624; 0xac37c];
     x_hsort := 0x84100 |}.

Definition ASAN_B_TEXT_LO : Z := 0x5dc34.
Definition ASAN_B_TEXT_N : nat := 289558.
Definition ASAN_B_MAIN : Z := 0xb4598.
Definition asan_b_init : acs := init_acs_of ASAN_B.
