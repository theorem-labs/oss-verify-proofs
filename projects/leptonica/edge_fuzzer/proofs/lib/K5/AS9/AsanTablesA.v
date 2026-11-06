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
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x72e000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x90154; rw_lo := 0x1bd000; rw_len := 0x571000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0xca28c; x_imemcpy := 0xca210; x_memset := 0x1b63dc; x_memcpy := 0x1b5fa8; x_memiszero := 0xca7d8;
     x_istrncpy := 0xca6b8; x_sealed := 0x12712; x_popfree := 0x968f0;
     x_sniff := 0xcb8f0; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0x1a5e20; x_envscan_k := 0x1a5e2c; x_pnscan := 0x1a5ee4; x_pnscan_k := 0x1a5ef0;
     stops_more := [0x94564; 0x95b88; 0xb9fe4; 0xc083c; 0xc0850; 0xc0864; 0xc6308; 0xc63d8; 0xd3920; 0xd482c; 0xd49bc; 0xde714];
     x_hsort := 0xb68f8 |}.

Definition ASAN_A_TEXT_LO : Z := 0x90154.
Definition ASAN_A_TEXT_N : nat := 307300.
Definition ASAN_A_MAIN : Z := 0xe6bdc.
Definition asan_a_init : acs := init_acs_of ASAN_A.

(* [comment removed for export] *)
