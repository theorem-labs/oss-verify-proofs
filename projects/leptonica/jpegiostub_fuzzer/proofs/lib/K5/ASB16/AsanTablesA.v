(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x628000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3af74; rw_lo := 0xc5000; rw_len := 0x563000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x6f970; x_imemcpy := 0x6f8f4; x_memset := 0xbf848; x_memcpy := 0xbf444; x_memiszero := 0x6fea0;
     x_istrncpy := 0x6fd9c; x_sealed := 0x11a1d; x_popfree := 0x41704;
     x_sniff := 0x70fb8; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xb4fcc; x_envscan_k := 0xb4fd8; x_pnscan := 0xb5090; x_pnscan_k := 0xb509c;
     stops_more := [0x3f378; 0x4099c; 0x5f6c8; 0x65f20; 0x65f34; 0x65f48; 0x6b9ec; 0x6babc; 0x78fe8; 0x79ef4; 0x7a084; 0x7a1f4; 0x83ddc];
     x_hsort := 0x5c34c |}.

Definition ASAN_A_TEXT_LO : Z := 0x3af74.
Definition ASAN_A_TEXT_N : nat := 141058.
Definition ASAN_A_MAIN : Z := 0x8bff8.
Definition asan_a_init : acs := init_acs_of ASAN_A.
