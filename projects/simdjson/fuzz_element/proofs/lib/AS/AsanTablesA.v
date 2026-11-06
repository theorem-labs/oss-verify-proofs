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

Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x6ca000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x5a424; rw_lo := 0x164000; rw_len := 0x566000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x94ac4; x_imemcpy := 0x94a48; x_memset := 0x15c928; x_memcpy := 0x15c524; x_memiszero := 0x95010;
     x_istrncpy := 0x94ef0; x_sealed := 0x11b38; x_popfree := 0x60ad4;
     x_sniff := 0x96128; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x14a9f0; x_envscan_k := 0x14a9fc; x_pnscan := 0x14aab4; x_pnscan_k := 0x14aac0;
     stops_more := [0x5e748; 0x5fd6c; 0x84640; 0x8b188; 0x8b19c; 0x8b1b0; 0x90b40; 0x90c10; 0x9e158; 0x9f064; 0x9f1f4; 0xa8f4c];
     x_hsort := 0x80cd0 |}.

Definition ASAN_A_TEXT_LO : Z := 0x5a424.
Definition ASAN_A_TEXT_N : nat := 271103.
Definition ASAN_A_MAIN : Z := 0xb1168.
Definition asan_a_init : acs := init_acs_of ASAN_A.
