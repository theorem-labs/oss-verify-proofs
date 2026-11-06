(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x785000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x9fa94; rw_lo := 0x20b000; rw_len := 0x57a000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0xdcc54; x_imemcpy := 0xdcbd8; x_memset := 0x203df0; x_memcpy := 0x2039bc; x_memiszero := 0xdd1a0;
     x_istrncpy := 0xdd080; x_sealed := 0x12a7d; x_popfree := 0xa6230;
     x_sniff := 0xde2b8; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0x1f254c; x_envscan_k := 0x1f2558; x_pnscan := 0x1f2610; x_pnscan_k := 0x1f261c;
     stops_more := [0xa3ea4; 0xa54c8; 0xcc998; 0xd3204; 0xd3218; 0xd322c; 0xd8cd0; 0xd8da0; 0xe6314; 0xe724c; 0xe73dc; 0xf1164];
     x_hsort := 0xc92ac |}.

Definition ASAN_A_TEXT_LO : Z := 0x9fa94.
Definition ASAN_A_TEXT_N : nat := 370962.
Definition ASAN_A_MAIN : Z := 0xf962c.
Definition asan_a_init : acs := init_acs_of ASAN_A.
