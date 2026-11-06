(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: emitted for reac-pw/fuzz_headamp image B by atable.py e88affcf0526 (the start-up tool set at f1417943331) from fuzz_headamp.asan-ubsan and its unstripped twin: TFIB_TEXT_N over this image's own .text, img_lo / img_hi cited from lib/Reusable/YImgTop.v. *)
(* Read from: fuzz_headamp.asan-ubsan (reac-pw/fuzz_headamp asan-ubsan) sha256 53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; unstripped twin sha256 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YImgTop.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := YImgTop.IMG_LO; img_hi := YImgTop.IMG_TOP; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30764; rw_lo := 0x9e000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x64118; x_imemcpy := 0x6409c; x_memset := 0x95d28; x_memcpy := 0x95924; x_memiszero := 0x64648;
x_istrncpy := 0x64544; x_sealed := 0x11877; x_popfree := 0x36b50;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8c00c; x_envscan_k := 0x8c018; x_pnscan := 0x8c0d0; x_pnscan_k := 0x8c0dc;
stops_more := [0x347c4; 0x35de8; 0x54424; 0x5a7dc; 0x5a7f0; 0x5a804; 0x60194; 0x60264; 0x6d790; 0x6e69c; 0x6e82c; 0x78584; 0x6e99c]
|}.
Definition TFIB_TEXT_LO : Z := 0x30764.
Definition TFIB_TEXT_N : nat := 109142.
Lemma TFIB_img_lo_val : img_lo TFIB = 0x10000.
Proof. reflexivity. Qed.
Lemma TFIB_img_hi_val : img_hi TFIB = 0x5fa000.
Proof. reflexivity. Qed.
