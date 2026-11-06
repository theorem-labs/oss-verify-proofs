(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x62c000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3c094; rw_lo := 0xc9000; rw_len := 0x563000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x70a90; x_imemcpy := 0x70a14; x_memset := 0xc2f10; x_memcpy := 0xc2b0c; x_memiszero := 0x70fc0;
     x_istrncpy := 0x70ebc; x_sealed := 0x11a68; x_popfree := 0x42824;
     x_sniff := 0x720d8; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xb8694; x_envscan_k := 0xb86a0; x_pnscan := 0xb8758; x_pnscan_k := 0xb8764;
     stops_more := [0x40498; 0x41abc; 0x607e8; 0x67040; 0x67054; 0x67068; 0x6cb0c; 0x6cbdc; 0x7a108; 0x7b014; 0x7b1a4; 0x7b314; 0x84efc];
     x_hsort := 0x5d46c |}.

Definition ASAN_A_TEXT_LO : Z := 0x3c094.
Definition ASAN_A_TEXT_N : nat := 143468.
Definition ASAN_A_MAIN : Z := 0x8d118.
Definition asan_a_init : acs := init_acs_of ASAN_A.
