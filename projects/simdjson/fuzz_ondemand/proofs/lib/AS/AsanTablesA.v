(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x66b000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x446a8; rw_lo := 0x109000; rw_len := 0x562000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x79e7c; x_imemcpy := 0x79e00; x_memset := 0x102e0c; x_memcpy := 0x102a08; x_memiszero := 0x7a3ac;
     x_istrncpy := 0x7a2a8; x_sealed := 0x11a93; x_popfree := 0x4ad58;
     x_sniff := 0x7b4c4; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0xf3d60; x_envscan_k := 0xf3d6c; x_pnscan := 0xf3e24; x_pnscan_k := 0xf3e30;
     stops_more := [0x489cc; 0x49ff0; 0x699f8; 0x70540; 0x70554; 0x70568; 0x75ef8; 0x75fc8; 0x834f4; 0x84400; 0x84590; 0x8e2e8];
     x_hsort := 0x66088 |}.

Definition ASAN_A_TEXT_LO : Z := 0x446a8.
Definition ASAN_A_TEXT_N : nat := 200416.
Definition ASAN_A_MAIN : Z := 0x96504.
Definition asan_a_init : acs := init_acs_of ASAN_A.
