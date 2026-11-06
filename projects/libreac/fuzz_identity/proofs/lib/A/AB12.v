(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the atable of libreac/fuzz_identity image A, emitted by atable.py (projects/libreac/fuzz_disco/proofs/provenance/evidence/startup-Y/yb12/atable.py, sha256 05c6070b6635) from this image and its unstripped twin with --img-names YImgTop.IMG_LO,YImgTop.IMG_TOP, except TFIB_TEXT_N: atable.py writes 107725, and this file has 107749, all of the image's .text ((0x99d4c - 0x309b8) / 4) *)
(* Read from: fuzz_identity.asan (libreac/fuzz_identity asan) sha256 c954b804786cb87fc218414447199e35235b9788453ec0db312f97cd0dc4291b; unstripped twin sha256 5b0cbe57303630895c71979f5c3209f1d343f0f42aad36e87c9f5193408da124 *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YImgTop.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := YImgTop.IMG_LO; img_hi := YImgTop.IMG_TOP; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x309b8; rw_lo := 0x9e000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x63be4; x_imemcpy := 0x63b68; x_memset := 0x94a18; x_memcpy := 0x94614; x_memiszero := 0x64114;
x_istrncpy := 0x64010; x_sealed := 0x11837; x_popfree := 0x36da4;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8a418; x_envscan_k := 0x8a424; x_pnscan := 0x8a4dc; x_pnscan_k := 0x8a4e8;
stops_more := [0x34a18; 0x3603c; 0x53ef0; 0x5a2a8; 0x5a2bc; 0x5a2d0; 0x5fc60; 0x5fd30; 0x6d25c; 0x6e168; 0x6e2f8; 0x78050]
|}.
Definition TFIB_TEXT_LO : Z := 0x309b8.
Definition TFIB_TEXT_N : nat := 107749.
Lemma TFIB_img_lo_val : img_lo TFIB = 0x10000.
Proof. reflexivity. Qed.
Lemma TFIB_img_hi_val : img_hi TFIB = 0x5fa000.
Proof. reflexivity. Qed.
