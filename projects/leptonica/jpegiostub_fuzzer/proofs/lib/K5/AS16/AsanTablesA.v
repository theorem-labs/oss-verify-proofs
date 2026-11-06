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
  {| img_lo := 0x10000; img_hi := 0x627000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3adc4; rw_lo := 0xc5000; rw_len := 0x562000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x6f7c0; x_imemcpy := 0x6f744; x_memset := 0xbef70; x_memcpy := 0xbeb6c; x_memiszero := 0x6fcf0;
     x_istrncpy := 0x6fbec; x_sealed := 0x11a08; x_popfree := 0x41554;
     x_sniff := 0x70e08; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xb46f4; x_envscan_k := 0xb4700; x_pnscan := 0xb47b8; x_pnscan_k := 0xb47c4;
     stops_more := [0x3f1c8; 0x407ec; 0x5f518; 0x65d70; 0x65d84; 0x65d98; 0x6b83c; 0x6b90c; 0x78e38; 0x79d44; 0x79ed4; 0x7a044; 0x83c2c];
     x_hsort := 0x5c19c |}.

Definition ASAN_A_TEXT_LO : Z := 0x3adc4.
Definition ASAN_A_TEXT_N : nat := 140600.
Definition ASAN_A_MAIN : Z := 0x8be48.
Definition asan_a_init : acs := init_acs_of ASAN_A.
