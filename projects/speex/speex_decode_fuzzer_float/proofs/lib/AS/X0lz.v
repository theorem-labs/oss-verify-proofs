(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0m4 X0li.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

Definition ASAN_B : atable :=
{| img_lo := 0x10000; img_hi := 0x65b000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x449a8; rw_lo := 0xf7000; rw_len := 0x564000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x79c2c; x_imemcpy := 0x79bb0; x_memset := 0xf1af8; x_memcpy := 0xf16f4; x_memiszero := 0x7a15c;
x_istrncpy := 0x7a058; x_sealed := 0x11d01; x_popfree := 0x4b138;
x_sniff := 0x7b274; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0xe63fc; x_envscan_k := 0xe6408; x_pnscan := 0xe64c0; x_pnscan_k := 0xe64cc;
stops_more := [0x48dac; 0x4a3d0; 0x69984; 0x701dc; 0x701f0; 0x70204; 0x75ca8; 0x75d78; 0x832a4; 0x841b0; 0x84340; 0x8e098];
x_hsort := 0x66298 |}.

Definition ASAN_B_TEXT_LO : Z := 0x449a8.
Definition ASAN_B_TEXT_N : nat := 182561.
Definition ASAN_B_MAIN : Z := 0x962b4.
Definition asan_b_init : acs := init_acs_of ASAN_B.
