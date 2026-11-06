(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Ported to libreac/fuzz_knock by a Theorem Labs lane from proofs/cgif/cgif_file_fuzzer/lib/A/AB12.v at c8557374ad2: module paths renamed; image values re-derived from fuzz_knock.asan (sha256 61768cf4..), as listed in the commit message. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AB12.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from libreac/fuzz_knock's asan image to its asan-ubsan image. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YImgTop.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := YImgTop.IMG_LO; img_hi := YImgTop.IMG_TOP; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x2fa9c; rw_lo := 0x98000; rw_len := 0x55b000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x623a8; x_imemcpy := 0x6232c; x_memset := 0x8fd50; x_memcpy := 0x8f94c; x_memiszero := 0x628d8;
x_istrncpy := 0x627d4; x_sealed := 0x117ee; x_popfree := 0x35e88;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x85754; x_envscan_k := 0x85760; x_pnscan := 0x85818; x_pnscan_k := 0x85824;
stops_more := [0x33afc; 0x35120; 0x526b4; 0x58a6c; 0x58a80; 0x58a94; 0x5e424; 0x5e4f4; 0x6ba20; 0x6c92c; 0x6cabc; 0x76814]
|}.
Definition TFIB_TEXT_LO : Z := 0x2fa9c.
Definition TFIB_TEXT_N : nat := 103802.
Lemma TFIB_img_lo_val : img_lo TFIB = 0x10000.
Proof. reflexivity. Qed.
Lemma TFIB_img_hi_val : img_hi TFIB = 0x5f3000.
Proof. reflexivity. Qed.
