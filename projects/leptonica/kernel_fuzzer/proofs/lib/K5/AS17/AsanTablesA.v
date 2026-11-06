(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x629000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3b514; rw_lo := 0xc6000; rw_len := 0x563000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x6ff10; x_imemcpy := 0x6fe94; x_memset := 0xc0798; x_memcpy := 0xc0394; x_memiszero := 0x70440;
     x_istrncpy := 0x7033c; x_sealed := 0x119ef; x_popfree := 0x41ca4;
     x_sniff := 0x71558; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xb5f1c; x_envscan_k := 0xb5f28; x_pnscan := 0xb5fe0; x_pnscan_k := 0xb5fec;
     stops_more := [0x3f918; 0x40f3c; 0x5fc68; 0x664c0; 0x664d4; 0x664e8; 0x6bf8c; 0x6c05c; 0x79588; 0x7a494; 0x7a624; 0x7a794; 0x8437c];
     x_hsort := 0x5c8ec |}.

Definition ASAN_A_TEXT_LO : Z := 0x3b514.
Definition ASAN_A_TEXT_N : nat := 141678.
Definition ASAN_A_MAIN : Z := 0x8c598.
Definition asan_a_init : acs := init_acs_of ASAN_A.
