(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs: emitted for reac-pw/fuzz_role image B by atable.py 6a35bb77e745 from fuzz_role.asan-ubsan and its unstripped twin, from proofs/cgif/cgif_file_fuzzer/lib/YB12.v at c8557374ad2e: TFIB_TEXT_N over this image's own .text, img_lo / img_hi cited from lib/Reusable/YImgTop.v *)
(* Read from: fuzz_role.asan-ubsan (reac-pw/fuzz_role asan-ubsan) sha256 b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; unstripped twin sha256 dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YImgTop.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := YImgTop.IMG_LO; img_hi := YImgTop.IMG_TOP; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x306ac; rw_lo := 0x9c000; rw_len := 0x55c000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x634f8; x_imemcpy := 0x6347c; x_memset := 0x94050; x_memcpy := 0x93c4c; x_memiszero := 0x63a28;
x_istrncpy := 0x63924; x_sealed := 0x11880; x_popfree := 0x36a98;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8a334; x_envscan_k := 0x8a340; x_pnscan := 0x8a3f8; x_pnscan_k := 0x8a404;
stops_more := [0x3470c; 0x35d30; 0x53804; 0x59bbc; 0x59bd0; 0x59be4; 0x5f574; 0x5f644; 0x6cb70; 0x6da7c; 0x6dc0c; 0x77964; 0x6dd7c]
|}.
Definition TFIB_TEXT_LO : Z := 0x306ac.
Definition TFIB_TEXT_N : nat := 107318.
Lemma TFIB_img_lo_val : img_lo TFIB = 0x10000.
Proof. reflexivity. Qed.
Lemma TFIB_img_hi_val : img_hi TFIB = 0x5f8000.
Proof. reflexivity. Qed.
