(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB12.v, with its module paths changed and its addresses moved to libreac/fuzz_disco's ASan build; the image top is YImgTop.IMG_TOP in place of a literal. *)
(* Modified by Theorem Labs, 2026-10: TFIB_TEXT_N is fuzz_disco.asan's own .text size / 4 (sha256 5e39150dd810: .text [0x30eac, 0x9eea8), 0x6dffc bytes), so the word table covers every function of the image. *)
(* Override record: TFIB_TEXT_N hand-set to own .text size / 4 (112639), STREAM-LEAD-CURRENT item 1i, overriding atable b9aa677211b7's donor-end value (112615). A later atable re-run must keep 112639. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YImgTop.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := YImgTop.IMG_LO; img_hi := YImgTop.IMG_TOP; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30eac; rw_lo := 0xa2000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x6441c; x_imemcpy := 0x643a0; x_memset := 0x99b74; x_memcpy := 0x99770; x_memiszero := 0x6494c;
x_istrncpy := 0x64848; x_sealed := 0x11835; x_popfree := 0x37298;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8f574; x_envscan_k := 0x8f580; x_pnscan := 0x8f638; x_pnscan_k := 0x8f644;
stops_more := [0x34f0c; 0x36530; 0x54728; 0x5aae0; 0x5aaf4; 0x5ab08; 0x60498; 0x60568; 0x6da94; 0x6e9a0; 0x6eb30; 0x78888]
|}.
Definition TFIB_TEXT_LO : Z := 0x30eac.
Definition TFIB_TEXT_N : nat := 112639.
Lemma TFIB_img_lo_val : img_lo TFIB = 0x10000.
Proof. reflexivity. Qed.
Lemma TFIB_img_hi_val : img_hi TFIB = 0x5fe000.
Proof. reflexivity. Qed.
