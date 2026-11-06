(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs: emitted for reac-pw/fuzz_pin image B by atable.py 6a35bb77e745 (the start-up tool set at tools commit 96d2c32e287) from fuzz_pin.asan-ubsan and its unstripped twin; TFIB_TEXT_N covers this image's own whole .text (0x3031c, 105005 words); stops_more is the image's 13 self-loops. *)
(* Read from: fuzz_pin.asan-ubsan (reac-pw/fuzz_pin asan-ubsan) sha256 d6f83d30152279dadae39fc626707a0037090a8909a186dac3c362b12088201f; unstripped twin sha256 635d02c7e8fa2e1653012207b6ddd2f2c5dd3b8e578ee9607cdc35b94e5260bb *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5f6000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x3031c; rw_lo := 0x9a000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x63b8c; x_imemcpy := 0x63b10; x_memset := 0x91724; x_memcpy := 0x91320; x_memiszero := 0x640bc;
x_istrncpy := 0x63fb8; x_sealed := 0x1181b; x_popfree := 0x36708;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x87124; x_envscan_k := 0x87130; x_pnscan := 0x871e8; x_pnscan_k := 0x871f4;
stops_more := [0x3437c; 0x359a0; 0x53e98; 0x5a250; 0x5a264; 0x5a278; 0x5fc08; 0x5fcd8; 0x6d204; 0x6e110; 0x6e2a0; 0x77ff8; 0x6e410]
|}.
Definition TFIB_TEXT_LO : Z := 0x3031c.
Definition TFIB_TEXT_N : nat := 105005.
