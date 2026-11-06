(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x6c1000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x57f20; rw_lo := 0x15c000; rw_len := 0x565000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x91c94; x_imemcpy := 0x91c18; x_memset := 0x1549b8; x_memcpy := 0x1545b4; x_memiszero := 0x921e0;
     x_istrncpy := 0x920c0; x_sealed := 0x11b10; x_popfree := 0x5e5d0;
     x_sniff := 0x932f8; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x142a80; x_envscan_k := 0x142a8c; x_pnscan := 0x142b44; x_pnscan_k := 0x142b50;
     stops_more := [0x5c244; 0x5d868; 0x81d50; 0x88358; 0x8836c; 0x88380; 0x8dd10; 0x8dde0; 0x9b328; 0x9c234; 0x9c3c4; 0xa611c];
     x_hsort := 0x7e3e0 |}.

Definition ASAN_A_TEXT_LO : Z := 0x57f20.
Definition ASAN_A_TEXT_N : nat := 265267.
Definition ASAN_A_MAIN : Z := 0xae338.
Definition asan_a_init : acs := init_acs_of ASAN_A.
