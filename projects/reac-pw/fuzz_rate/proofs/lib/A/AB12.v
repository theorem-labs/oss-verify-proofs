(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: emitted for reac-pw/fuzz_rate image A by atable.py e88affcf0526 from fuzz_rate.asan and its unstripped twin, from proofs/cgif/cgif_file_fuzzer/lib/A/AB12.v at c8557374ad2e: TFIB_TEXT_N over this image's own .text, img_lo / img_hi cited from lib/Reusable/YImgTop.v *)
(* Read from: fuzz_rate.asan (reac-pw/fuzz_rate asan) sha256 22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; unstripped twin sha256 0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3 *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YImgTop.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := YImgTop.IMG_LO; img_hi := YImgTop.IMG_TOP; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x309d4; rw_lo := 0x9d000; rw_len := 0x55d000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x63bec; x_imemcpy := 0x63b70; x_memset := 0x95358; x_memcpy := 0x94f54; x_memiszero := 0x6411c;
x_istrncpy := 0x64018; x_sealed := 0x11855; x_popfree := 0x36dc0;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8b638; x_envscan_k := 0x8b644; x_pnscan := 0x8b6fc; x_pnscan_k := 0x8b708;
stops_more := [0x34a34; 0x36058; 0x53ef8; 0x5a2b0; 0x5a2c4; 0x5a2d8; 0x5fc68; 0x5fd38; 0x6d264; 0x6e170; 0x6e300; 0x78058; 0x6e470]
|}.
Definition TFIB_TEXT_LO : Z := 0x309d4.
Definition TFIB_TEXT_N : nat := 108334.
Lemma TFIB_img_lo_val : img_lo TFIB = 0x10000.
Proof. reflexivity. Qed.
Lemma TFIB_img_hi_val : img_hi TFIB = 0x5fa000.
Proof. reflexivity. Qed.
