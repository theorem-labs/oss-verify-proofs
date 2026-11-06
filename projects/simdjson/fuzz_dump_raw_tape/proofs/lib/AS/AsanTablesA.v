(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x6c2000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x58618; rw_lo := 0x15d000; rw_len := 0x565000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x92364; x_imemcpy := 0x922e8; x_memset := 0x1558ac; x_memcpy := 0x1554a8; x_memiszero := 0x928b0;
     x_istrncpy := 0x92790; x_sealed := 0x11b28; x_popfree := 0x5ecc8;
     x_sniff := 0x939c8; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x143974; x_envscan_k := 0x143980; x_pnscan := 0x143a38; x_pnscan_k := 0x143a44;
     stops_more := [0x5c93c; 0x5df60; 0x82420; 0x88a28; 0x88a3c; 0x88a50; 0x8e3e0; 0x8e4b0; 0x9b9f8; 0x9c904; 0x9ca94; 0xa67ec];
     x_hsort := 0x7eab0 |}.

Definition ASAN_A_TEXT_LO : Z := 0x58618.
Definition ASAN_A_TEXT_N : nat := 265778.
Definition ASAN_A_MAIN : Z := 0xaea08.
Definition asan_a_init : acs := init_acs_of ASAN_A.
