(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5fb000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x302dc; rw_lo := 0x9f000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x63968; x_imemcpy := 0x638ec; x_memset := 0x97698; x_memcpy := 0x97294; x_memiszero := 0x63e98;
x_istrncpy := 0x63d94; x_sealed := 0x11806; x_popfree := 0x366c8;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8cc20; x_envscan_k := 0x8cc2c; x_pnscan := 0x8cce4; x_pnscan_k := 0x8ccf0;
stops_more := [0x3433c; 0x35960; 0x53c74; 0x5a02c; 0x5a040; 0x5a054; 0x5f9e4; 0x5fab4; 0x6cfe0; 0x6deec; 0x6e07c; 0x77dd4]
|}.
Definition TFIB_TEXT_LO : Z := 0x302dc.
Definition TFIB_TEXT_N : nat := 111012.
