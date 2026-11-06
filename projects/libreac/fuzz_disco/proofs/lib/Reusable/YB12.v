(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Generated for fuzz_disco's asan-ubsan image, not relocated from the donor: every field below is read from that
   image. Addresses come from a Theorem Labs lane's resolve_code.py function pairing (the donor is stripped, so a field that
   names a function is paired by content and taken at the donor's offset inside the paired function), the ELF
   header and its program headers, and a Theorem Labs lane's gen_symtab.py output. The image bounds cite YImgTop. *)
(* Modified by Theorem Labs, 2026-10: TFIB_TEXT_N hand-set to own .text size / 4 (A 112639 / Y 112841), STREAM-LEAD-CURRENT item 1i, overriding atable b9aa677211b7's donor-end value: own .text end, .text 0x30f24..0x9f248 of fuzz_disco.asan-ubsan (sha256 cee6f04ad3d4). *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YImgTop.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := YImgTop.IMG_LO; img_hi := YImgTop.IMG_TOP; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30f24; rw_lo := 0xa2000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x64494; x_imemcpy := 0x64418; x_memset := 0x99f14; x_memcpy := 0x99b10; x_memiszero := 0x649c4;
x_istrncpy := 0x648c0; x_sealed := 0x11835; x_popfree := 0x37310;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8f914; x_envscan_k := 0x8f920; x_pnscan := 0x8f9d8; x_pnscan_k := 0x8f9e4;
stops_more := [0x34f84; 0x365a8; 0x547a0; 0x5ab58; 0x5ab6c; 0x5ab80; 0x60510; 0x605e0; 0x6db0c; 0x6ea18; 0x6eba8; 0x78900]
|}.
Definition TFIB_TEXT_LO : Z := 0x30f24.
Definition TFIB_TEXT_N : nat := 112841.
Lemma TFIB_img_lo_val : img_lo TFIB = 0x10000.
Proof. reflexivity. Qed.
Lemma TFIB_img_hi_val : img_hi TFIB = 0x5fe000.
Proof. reflexivity. Qed.
