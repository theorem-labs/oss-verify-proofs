(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/libreac/fuzz_disco/lib/Reusable/YB12.v, with its module paths, addresses and numbers changed. *)
(* Read from: fuzz_identity.asan-ubsan (libreac/fuzz_identity asan-ubsan) sha256 baf1a4d065e02f55521d39f05d8c8d9ed763a0ef798c70cc3eabe5816ffb3f66; unstripped twin sha256 43b44d50be8a5e68f626662181c9cc17c0e0fef138e55f3c8bab371987a9c064 *)
(* Modified by Theorem Labs, 2026-10-29: re-emitted at the release's two-image path lib/ReusableB/YB12.v with the same content as before, only its Require paths mapped to the release layout (lib.B.A* -> lib.ReusableB.Y*, image-specific Reusable modules -> lib.ReusableB). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB Require Import YK09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YImgTop.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := YImgTop.IMG_LO; img_hi := YImgTop.IMG_TOP; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30a20; rw_lo := 0x9e000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x63c4c; x_imemcpy := 0x63bd0; x_memset := 0x94d04; x_memcpy := 0x94900; x_memiszero := 0x6417c;
x_istrncpy := 0x64078; x_sealed := 0x1183e; x_popfree := 0x36e0c;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8a704; x_envscan_k := 0x8a710; x_pnscan := 0x8a7c8; x_pnscan_k := 0x8a7d4;
stops_more := [0x34a80; 0x360a4; 0x53f58; 0x5a310; 0x5a324; 0x5a338; 0x5fcc8; 0x5fd98; 0x6d2c4; 0x6e1d0; 0x6e360; 0x780b8]
|}.
Definition TFIB_TEXT_LO : Z := 0x30a20.
Definition TFIB_TEXT_N : nat := 107910.
Lemma TFIB_img_lo_val : img_lo TFIB = 0x10000.
Proof. reflexivity. Qed.
Lemma TFIB_img_hi_val : img_hi TFIB = 0x5fa000.
Proof. reflexivity. Qed.
