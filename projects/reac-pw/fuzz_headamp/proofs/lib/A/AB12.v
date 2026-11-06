(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AB12.v at c8557374ad2e; emitted for reac-pw/fuzz_headamp image A by atable.py e88affcf0526 from fuzz_headamp.asan and its unstripped twin: every field read from this image, TFIB_TEXT_N over this image's own .text, stops_more the image's own self-loops; img_lo / img_hi cited from lib/Reusable/YImgTop.v; module paths changed. *)
(* Read from: fuzz_headamp.asan (reac-pw/fuzz_headamp asan) sha256 f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; unstripped twin sha256 b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YImgTop.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := YImgTop.IMG_LO; img_hi := YImgTop.IMG_TOP; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x306e4; rw_lo := 0x9e000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x64098; x_imemcpy := 0x6401c; x_memset := 0x958b0; x_memcpy := 0x954ac; x_memiszero := 0x645c8;
x_istrncpy := 0x644c4; x_sealed := 0x11860; x_popfree := 0x36ad0;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8bb94; x_envscan_k := 0x8bba0; x_pnscan := 0x8bc58; x_pnscan_k := 0x8bc64;
stops_more := [0x34744; 0x35d68; 0x543a4; 0x5a75c; 0x5a770; 0x5a784; 0x60114; 0x601e4; 0x6d710; 0x6e61c; 0x6e7ac; 0x78504; 0x6e91c]
|}.
Definition TFIB_TEXT_LO : Z := 0x306e4.
Definition TFIB_TEXT_N : nat := 108888.
Lemma TFIB_img_lo_val : img_lo TFIB = 0x10000.
Proof. reflexivity. Qed.
Lemma TFIB_img_hi_val : img_hi TFIB = 0x5fa000.
Proof. reflexivity. Qed.
