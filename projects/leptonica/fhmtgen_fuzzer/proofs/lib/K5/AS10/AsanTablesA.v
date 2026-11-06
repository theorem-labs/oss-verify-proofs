(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x646000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3f5dc; rw_lo := 0xe0000; rw_len := 0x566000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x74320; x_imemcpy := 0x742a4; x_memset := 0xda744; x_memcpy := 0xda340; x_memiszero := 0x74850;
     x_istrncpy := 0x7474c; x_sealed := 0x11ab8; x_popfree := 0x45d6c;
     x_sniff := 0x75968; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xcfec8; x_envscan_k := 0xcfed4; x_pnscan := 0xcff8c; x_pnscan_k := 0xcff98;
     stops_more := [0x439e0; 0x45004; 0x64078; 0x6a8d0; 0x6a8e4; 0x6a8f8; 0x7039c; 0x7046c; 0x7d998; 0x7e8a4; 0x7ea34; 0x8878c];
     x_hsort := 0x60cfc |}.

Definition ASAN_A_TEXT_LO : Z := 0x3f5dc.
Definition ASAN_A_TEXT_N : nat := 164135.
Definition ASAN_A_MAIN : Z := 0x909a8.
Definition asan_a_init : acs := init_acs_of ASAN_A.

(* [comment removed for export] *)
