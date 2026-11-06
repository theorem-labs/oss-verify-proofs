(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

(* [comment removed for export] *)
Definition ASAN_A : atable :=
  {| img_lo := 0x10000; img_hi := 0x64e000; n_res := 4; shadow_off := 0x7fff8000;
     a_entry := 0x3f6dc; rw_lo := 0xe9000; rw_len := 0x565000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
     x_imemset := 0x74420; x_imemcpy := 0x743a4; x_memset := 0xe2fe8; x_memcpy := 0xe2be4; x_memiszero := 0x74950;
     x_istrncpy := 0x7484c; x_sealed := 0x11ad0; x_popfree := 0x45e6c;
     x_sniff := 0x75a68; sniff_tab := 0; sniff_cell := 0;   (* [comment removed for export] *)
     x_envscan := 0xd876c; x_envscan_k := 0xd8778; x_pnscan := 0xd8830; x_pnscan_k := 0xd883c;
     stops_more := [0x43ae0; 0x45104; 0x64178; 0x6a9d0; 0x6a9e4; 0x6a9f8; 0x7049c; 0x7056c; 0x7da98; 0x7e9a4; 0x7eb34; 0x8888c];
     x_hsort := 0x60dfc |}.

Definition ASAN_A_TEXT_LO : Z := 0x3f6dc.
Definition ASAN_A_TEXT_N : nat := 172816.
Definition ASAN_A_MAIN : Z := 0x90aa8.
Definition asan_a_init : acs := init_acs_of ASAN_A.

(* [comment removed for export] *)
