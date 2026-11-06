(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z78 Z2z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x669000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x446c4; rw_lo := 0x107000; rw_len := 0x562000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x79e88; x_imemcpy := 0x79e0c; x_memset := 0x1013ec; x_memcpy := 0x100fe8; x_memiszero := 0x7a3b8;
     x_istrncpy := 0x7a2b4; x_sealed := 0x11a6c; x_popfree := 0x4ad74;
     x_sniff := 0x7b4d0; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0xf2340; x_envscan_k := 0xf234c; x_pnscan := 0xf2404; x_pnscan_k := 0xf2410;
     stops_more := [0x489e8; 0x4a00c; 0x69a04; 0x7054c; 0x70560; 0x70574; 0x75f04; 0x75fd4; 0x83500; 0x8440c; 0x8459c; 0x8e2f4];
     x_hsort := 0x66094 |}.

Definition ASAN_A_TEXT_LO : Z := 0x446c4.
Definition ASAN_A_TEXT_N : nat := 198737.
Definition ASAN_A_MAIN : Z := 0x96510.
Definition asan_a_init : acs := init_acs_of ASAN_A.
