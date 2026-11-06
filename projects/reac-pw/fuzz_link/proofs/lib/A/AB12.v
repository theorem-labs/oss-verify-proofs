(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Read from: fuzz_link.asan (reac-pw/fuzz_link asan) sha256 059dae63e07ca2d80ae9227fa125d40586a02172c96d2b6884f8617ab912061d; unstripped twin sha256 66cd0f159895f119b29a44eb3760cfda78506402a019729057dba69562af9d9f *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK09.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := 0x10000; img_hi := 0x654000; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x3126c; rw_lo := 0xa3000; rw_len := 0x5b1000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x656a4; x_imemcpy := 0x65628; x_memset := 0x9afa8; x_memcpy := 0x9aba4; x_memiszero := 0x65bd4;
x_istrncpy := 0x65ad0; x_sealed := 0x11836; x_popfree := 0x37738;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x903a4; x_envscan_k := 0x903b0; x_pnscan := 0x90468; x_pnscan_k := 0x90474;
stops_more := [0x353ac; 0x369d0; 0x5564c; 0x5bc54; 0x5bc68; 0x5bc7c; 0x61720; 0x617f0; 0x6ed1c; 0x6fc28; 0x6fdb8; 0x79b10; 0x6ff28]
|}.
Definition TFIB_TEXT_LO : Z := 0x3126c.
Definition TFIB_TEXT_N : nat := 113716.
