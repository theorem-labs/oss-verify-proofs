(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB12.v, with its module paths changed and its addresses moved to plugin-hostd/fuzz_command's ASan build; TFIB_TEXT_N covers fuzz_command.asan's own whole .text, 0x33340..0xa46fc: its size / 4 = 115951 words. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x606000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x33340; rw_lo := 0xa8000; rw_len := 0x55e000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x699bc; x_imemcpy := 0x69940; x_memset := 0x9ef40; x_memcpy := 0x9eb3c; x_memiszero := 0x69eec;
x_istrncpy := 0x69de8; x_sealed := 0x11860; x_popfree := 0x3972c;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x9492c; x_envscan_k := 0x94938; x_pnscan := 0x949f0; x_pnscan_k := 0x949fc;
stops_more := [0x373a0; 0x389c4; 0x59cc8; 0x60080; 0x60094; 0x600a8; 0x65a38; 0x65b08; 0x73034; 0x73f40; 0x740d0; 0x7de28]
|}.
Definition TFIB_TEXT_LO : Z := 0x33340.
Definition TFIB_TEXT_N : nat := 115951.
