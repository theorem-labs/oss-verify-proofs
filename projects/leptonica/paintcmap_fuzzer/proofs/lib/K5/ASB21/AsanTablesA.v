(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x62d000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3bf28; rw_lo := 0xca000; rw_len := 0x563000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x70ac0; x_imemcpy := 0x70a44; x_memset := 0xc4420; x_memcpy := 0xc401c; x_memiszero := 0x70ff0;
     x_istrncpy := 0x70eec; x_sealed := 0x11a1b; x_popfree := 0x426b8;
     x_sniff := 0x72108; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xb9ba4; x_envscan_k := 0xb9bb0; x_pnscan := 0xb9c68; x_pnscan_k := 0xb9c74;
     stops_more := [0x4032c; 0x41950; 0x60818; 0x67070; 0x67084; 0x67098; 0x6cb3c; 0x6cc0c; 0x7a138; 0x7b044; 0x7b1d4; 0x7b344; 0x84f2c];
     x_hsort := 0x5d49c |}.

Definition ASAN_A_TEXT_LO : Z := 0x3bf28.
Definition ASAN_A_TEXT_N : nat := 144907.
Definition ASAN_A_MAIN : Z := 0x8d148.
Definition asan_a_init : acs := init_acs_of ASAN_A.
