(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: emitted for reac-pw/fuzz_pin image A by atable.py 6a35bb77e745 (the start-up tool set at tools commit 96d2c32e287) from fuzz_pin.asan and its unstripped twin; TFIB_TEXT_N covers this image's own whole .text (0x3031c, 104938 words); stops_more is the image's 13 self-loops. *)
(* Read from: fuzz_pin.asan (reac-pw/fuzz_pin asan) sha256 3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16; unstripped twin sha256 435309a6b12c4d3e09a8484ec253b5fab600e4f00c28694ac28db2fc7a4475ab *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x5f6000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x3031c; rw_lo := 0x9a000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x63b8c; x_imemcpy := 0x63b10; x_memset := 0x91618; x_memcpy := 0x91214; x_memiszero := 0x640bc;
x_istrncpy := 0x63fb8; x_sealed := 0x1181b; x_popfree := 0x36708;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x87018; x_envscan_k := 0x87024; x_pnscan := 0x870dc; x_pnscan_k := 0x870e8;
stops_more := [0x3437c; 0x359a0; 0x53e98; 0x5a250; 0x5a264; 0x5a278; 0x5fc08; 0x5fcd8; 0x6d204; 0x6e110; 0x6e2a0; 0x77ff8; 0x6e410]
|}.
Definition TFIB_TEXT_LO : Z := 0x3031c.
Definition TFIB_TEXT_N : nat := 104938.
