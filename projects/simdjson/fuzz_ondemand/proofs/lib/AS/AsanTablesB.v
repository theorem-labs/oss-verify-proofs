(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

Definition ASAN_B : atable :=
  {| img_lo := 0x10000; img_hi := 0x679000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x44644; rw_lo := 0x117000; rw_len := 0x562000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x79e18; x_imemcpy := 0x79d9c; x_memset := 0x110f9c; x_memcpy := 0x110b98; x_memiszero := 0x7a348;
     x_istrncpy := 0x7a244; x_sealed := 0x11aaf; x_popfree := 0x4acf4;
     x_sniff := 0x7b460; sniff_tab := 0; sniff_cell := 0;
     x_envscan := 0x101ef0; x_envscan_k := 0x101efc; x_pnscan := 0x101fb4; x_pnscan_k := 0x101fc0;
     stops_more := [0x48968; 0x49f8c; 0x69994; 0x704dc; 0x704f0; 0x70504; 0x75e94; 0x75f64; 0x83490; 0x8439c; 0x8452c; 0x8e284];
     x_hsort := 0x66024 |}.

Definition ASAN_B_TEXT_LO : Z := 0x44644.
Definition ASAN_B_TEXT_N : nat := 214877.
Definition ASAN_B_MAIN : Z := 0x964a0.
Definition asan_b_init : acs := init_acs_of ASAN_B.
