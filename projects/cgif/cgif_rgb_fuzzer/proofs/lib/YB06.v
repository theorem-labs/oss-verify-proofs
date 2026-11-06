(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0a.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TRA : atable :=
{| img_lo := 0x10000; img_hi := 0x5ff000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x306d8; rw_lo := 0xa3000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x64484; x_imemcpy := 0x64408; x_memset := 0x9b894; x_memcpy := 0x9b490; x_memiszero := 0x649b4;
x_istrncpy := 0x648b0; x_sealed := 0x1182d; x_popfree := 0x36cd0;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x90e1c; x_envscan_k := 0x90e28; x_pnscan := 0x90ee0; x_pnscan_k := 0x90eec;
stops_more := [0x34944; 0x35f68; 0x54790; 0x5ab48; 0x5ab5c; 0x5ab70; 0x60500; 0x605d0; 0x6dafc; 0x6ea08; 0x6eb98; 0x788f0]
|}.
Definition TRA_TEXT_LO : Z := 0x306d8.
Definition TRA_TEXT_N : nat := 110892.
Definition TFB : atable :=
{| img_lo := 0x10000; img_hi := 0x5da000  ; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30710; rw_lo := 0xa3000  ; rw_len := 0x53b000  ; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x64490 + 0x28; x_imemcpy := 0x64414 + 0x28; x_memset := 0x99d50 + 0x614; x_memcpy := 0x9994c + 0x614; x_memiszero := 0x649c0 + 0x28;
x_istrncpy := 0x648bc + 0x28; x_sealed := 0x1182d  ; x_popfree := 0x36ce0 + 0x28;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x906cc + 0x614; x_envscan_k := 0x906d8 + 0x614; x_pnscan := 0x90790 + 0x614; x_pnscan_k := 0x9079c + 0x614;
stops_more := map (fun z => z + 0x28) [0x34954; 0x35f78; 0x5479c; 0x5ab54; 0x5ab68; 0x5ab7c; 0x6050c; 0x605dc; 0x6db00; 0x6ea0c; 0x6eb9c; 0x788f4] |}.
