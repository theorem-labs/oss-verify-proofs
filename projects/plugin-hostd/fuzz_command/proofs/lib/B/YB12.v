(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB12.v, with its module paths changed and its addresses moved to plugin-hostd/fuzz_command's ASan+UBSan build; TFIB_TEXT_N covers fuzz_command.asan-ubsan's own whole .text, 0x3338c..0xa4258: its size / 4 = 115635 words. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x606000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x3338c; rw_lo := 0xa7000; rw_len := 0x55f000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x69a08; x_imemcpy := 0x6998c; x_memset := 0x9ea9c; x_memcpy := 0x9e698; x_memiszero := 0x69f38;
x_istrncpy := 0x69e34; x_sealed := 0x11860; x_popfree := 0x39778;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x94488; x_envscan_k := 0x94494; x_pnscan := 0x9454c; x_pnscan_k := 0x94558;
stops_more := [0x373ec; 0x38a10; 0x59d14; 0x600cc; 0x600e0; 0x600f4; 0x65a84; 0x65b54; 0x73080; 0x73f8c; 0x7411c; 0x7de74]
|}.
Definition TFIB_TEXT_LO : Z := 0x3338c.
Definition TFIB_TEXT_N : nat := 115635.
