(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x6d2000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x5da84; rw_lo := 0x16b000; rw_len := 0x567000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x97d38; x_imemcpy := 0x97cbc; x_memset := 0x1644d4; x_memcpy := 0x1640d0; x_memiszero := 0x98284;
     x_istrncpy := 0x98164; x_sealed := 0x11b8e; x_popfree := 0x64134;
     x_sniff := 0x9939c; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x151ffc; x_envscan_k := 0x152008; x_pnscan := 0x1520c0; x_pnscan_k := 0x1520cc;
     stops_more := [0x61da8; 0x633cc; 0x878b4; 0x8e3fc; 0x8e410; 0x8e424; 0x93db4; 0x93e84; 0xa13cc; 0xa22d8; 0xa2468; 0xac1c0];
     x_hsort := 0x83f44 |}.

Definition ASAN_A_TEXT_LO : Z := 0x5da84.
Definition ASAN_A_TEXT_N : nat := 275489.
Definition ASAN_A_MAIN : Z := 0xb43dc.
Definition asan_a_init : acs := init_acs_of ASAN_A.
