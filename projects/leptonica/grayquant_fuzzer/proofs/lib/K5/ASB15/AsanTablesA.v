(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x64d000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3f0fc; rw_lo := 0xe8000; rw_len := 0x565000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x73e40; x_imemcpy := 0x73dc4; x_memset := 0xe211c; x_memcpy := 0xe1d18; x_memiszero := 0x74370;
     x_istrncpy := 0x7426c; x_sealed := 0x11b3b; x_popfree := 0x4588c;
     x_sniff := 0x75488; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xd50e0; x_envscan_k := 0xd50ec; x_pnscan := 0xd51a4; x_pnscan_k := 0xd51b0;
     stops_more := [0x43500; 0x44b24; 0x63b98; 0x6a3f0; 0x6a404; 0x6a418; 0x6febc; 0x6ff8c; 0x7d4b8; 0x7e3c4; 0x7e554; 0x882ac];
     x_hsort := 0x6081c |}.

Definition ASAN_A_TEXT_LO : Z := 0x3f0fc.
Definition ASAN_A_TEXT_N : nat := 172245.
Definition ASAN_A_MAIN : Z := 0x904c8.
Definition asan_a_init : acs := init_acs_of ASAN_A.

(* [comment removed for export] *)
