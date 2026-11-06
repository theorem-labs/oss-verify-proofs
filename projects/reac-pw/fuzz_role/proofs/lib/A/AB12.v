(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: emitted for reac-pw/fuzz_role image A by atable.py 6a35bb77e745 from fuzz_role.asan and its unstripped twin, from proofs/cgif/cgif_file_fuzzer/lib/A/AB12.v at c8557374ad2e: TFIB_TEXT_N over this image's own .text, img_lo / img_hi cited from lib/Reusable/YImgTop.v *)
(* Read from: fuzz_role.asan (reac-pw/fuzz_role asan) sha256 614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; unstripped twin sha256 6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6 *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YImgTop.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := YImgTop.IMG_LO; img_hi := YImgTop.IMG_TOP; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30634; rw_lo := 0x9c000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x63460; x_imemcpy := 0x633e4; x_memset := 0x93db0; x_memcpy := 0x939ac; x_memiszero := 0x63990;
x_istrncpy := 0x6388c; x_sealed := 0x11869; x_popfree := 0x36a20;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8a094; x_envscan_k := 0x8a0a0; x_pnscan := 0x8a158; x_pnscan_k := 0x8a164;
stops_more := [0x34694; 0x35cb8; 0x5376c; 0x59b24; 0x59b38; 0x59b4c; 0x5f4dc; 0x5f5ac; 0x6cad8; 0x6d9e4; 0x6db74; 0x778cc; 0x6dce4]
|}.
Definition TFIB_TEXT_LO : Z := 0x30634.
Definition TFIB_TEXT_N : nat := 107180.
Lemma TFIB_img_lo_val : img_lo TFIB = 0x10000.
Proof. reflexivity. Qed.
Lemma TFIB_img_hi_val : img_hi TFIB = 0x5f8000.
Proof. reflexivity. Qed.
