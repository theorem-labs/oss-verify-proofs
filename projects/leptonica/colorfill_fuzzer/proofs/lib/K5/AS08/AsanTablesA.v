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
  {| img_lo := 0x10000; img_hi := 0x62b000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3bf0c; rw_lo := 0xc8000; rw_len := 0x563000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x70908; x_imemcpy := 0x7088c; x_memset := 0xc2538; x_memcpy := 0xc2134; x_memiszero := 0x70e38;
     x_istrncpy := 0x70d34; x_sealed := 0x11a53; x_popfree := 0x4269c;
     x_sniff := 0x71f50; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xb7cbc; x_envscan_k := 0xb7cc8; x_pnscan := 0xb7d80; x_pnscan_k := 0xb7d8c;
     stops_more := [0x40310; 0x41934; 0x60660; 0x66eb8; 0x66ecc; 0x66ee0; 0x6c984; 0x6ca54; 0x79f80; 0x7ae8c; 0x7b01c; 0x7b18c; 0x84d74];
     x_hsort := 0x5d2e4 |}.

Definition ASAN_A_TEXT_LO : Z := 0x3bf0c.
Definition ASAN_A_TEXT_N : nat := 142936.
Definition ASAN_A_MAIN : Z := 0x8cf90.
Definition asan_a_init : acs := init_acs_of ASAN_A.
