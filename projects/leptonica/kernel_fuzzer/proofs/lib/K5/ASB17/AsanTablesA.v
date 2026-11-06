(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x62a000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3b70c; rw_lo := 0xc7000; rw_len := 0x563000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x70108; x_imemcpy := 0x7008c; x_memset := 0xc12ac; x_memcpy := 0xc0ea8; x_memiszero := 0x70638;
     x_istrncpy := 0x70534; x_sealed := 0x11a04; x_popfree := 0x41e9c;
     x_sniff := 0x71750; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xb6a30; x_envscan_k := 0xb6a3c; x_pnscan := 0xb6af4; x_pnscan_k := 0xb6b00;
     stops_more := [0x3fb10; 0x41134; 0x5fe60; 0x666b8; 0x666cc; 0x666e0; 0x6c184; 0x6c254; 0x79780; 0x7a68c; 0x7a81c; 0x7a98c; 0x84574];
     x_hsort := 0x5cae4 |}.

Definition ASAN_A_TEXT_LO : Z := 0x3b70c.
Definition ASAN_A_TEXT_N : nat := 142261.
Definition ASAN_A_MAIN : Z := 0x8c790.
Definition asan_a_init : acs := init_acs_of ASAN_A.
