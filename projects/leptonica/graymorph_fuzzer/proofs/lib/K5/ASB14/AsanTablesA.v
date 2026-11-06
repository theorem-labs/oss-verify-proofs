(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x64b000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3ecfc; rw_lo := 0xe7000; rw_len := 0x564000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x738a4; x_imemcpy := 0x73828; x_memset := 0xe1014; x_memcpy := 0xe0c10; x_memiszero := 0x73dd4;
     x_istrncpy := 0x73cd0; x_sealed := 0x11ac0; x_popfree := 0x4548c;
     x_sniff := 0x74eec; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xd6798; x_envscan_k := 0xd67a4; x_pnscan := 0xd685c; x_pnscan_k := 0xd6868;
     stops_more := [0x43100; 0x44724; 0x635fc; 0x69e54; 0x69e68; 0x69e7c; 0x6f920; 0x6f9f0; 0x7cf1c; 0x7de28; 0x7dfb8; 0x7e128; 0x87d10];
     x_hsort := 0x60280 |}.

Definition ASAN_A_TEXT_LO : Z := 0x3ecfc.
Definition ASAN_A_TEXT_N : nat := 171411.
Definition ASAN_A_MAIN : Z := 0x8ff2c.
Definition asan_a_init : acs := init_acs_of ASAN_A.

(* [comment removed for export] *)
