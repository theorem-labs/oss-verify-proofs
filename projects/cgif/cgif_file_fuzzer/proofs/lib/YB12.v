(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5fb000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x3030c; rw_lo := 0x9f000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x63998; x_imemcpy := 0x6391c; x_memset := 0x9790c; x_memcpy := 0x97508; x_memiszero := 0x63ec8;
x_istrncpy := 0x63dc4; x_sealed := 0x11806; x_popfree := 0x366f8;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8ce94; x_envscan_k := 0x8cea0; x_pnscan := 0x8cf58; x_pnscan_k := 0x8cf64;
stops_more := [0x3436c; 0x35990; 0x53ca4; 0x5a05c; 0x5a070; 0x5a084; 0x5fa14; 0x5fae4; 0x6d010; 0x6df1c; 0x6e0ac; 0x77e04]
|}.
Definition TFIB_TEXT_LO : Z := 0x3030c.
Definition TFIB_TEXT_N : nat := 111037.
