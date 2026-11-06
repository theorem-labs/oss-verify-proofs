(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0m4 X0li.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import APC.

Definition ASAN_A : atable :=
{| img_lo := 0x10000; img_hi := 0x652000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x448bc; rw_lo := 0xef000; rw_len := 0x563000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x79b40; x_imemcpy := 0x79ac4; x_memset := 0xe9284; x_memcpy := 0xe8e80; x_memiszero := 0x7a070;
x_istrncpy := 0x79f6c; x_sealed := 0x11cc4; x_popfree := 0x4b04c;
x_sniff := 0x7b188; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0xddccc; x_envscan_k := 0xddcd8; x_pnscan := 0xddd90; x_pnscan_k := 0xddd9c;
stops_more := [0x48cc0; 0x4a2e4; 0x69898; 0x700f0; 0x70104; 0x70118; 0x75bbc; 0x75c8c; 0x831b8; 0x840c4; 0x84254; 0x8dfac];
x_hsort := 0x661ac |}.

Definition ASAN_A_TEXT_LO : Z := 0x448bc.
Definition ASAN_A_TEXT_N : nat := 173887.
Definition ASAN_A_MAIN : Z := 0x961c8.
Definition asan_a_init : acs := init_acs_of ASAN_A.
