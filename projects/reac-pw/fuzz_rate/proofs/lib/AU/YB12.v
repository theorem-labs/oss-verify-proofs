(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: emitted for reac-pw/fuzz_rate image B by atable.py e88affcf0526 from fuzz_rate.asan-ubsan and its unstripped twin, from proofs/cgif/cgif_file_fuzzer/lib/YB12.v at c8557374ad2e: TFIB_TEXT_N over this image's own .text, img_lo / img_hi cited from lib/Reusable/YImgTop.v; module paths changed *)
(* Read from: fuzz_rate.asan-ubsan (reac-pw/fuzz_rate asan-ubsan) sha256 c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; unstripped twin sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1 *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YImgTop.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope Z_scope.
Definition TFIB : atable :=
{| img_lo := YImgTop.IMG_LO; img_hi := YImgTop.IMG_TOP; n_res := 4; shadow_off := 0x7fff8000;
a_entry := 0x30a0c; rw_lo := 0x9d000; rw_len := 0x55d000; ph_addr_z := 0x10040; ph_ent_z := 56; ph_num_z := 11;
x_imemset := 0x63c44; x_imemcpy := 0x63bc8; x_memset := 0x95660; x_memcpy := 0x9525c; x_memiszero := 0x64174;
x_istrncpy := 0x64070; x_sealed := 0x118dd; x_popfree := 0x36df8;
x_sniff := 0; sniff_tab := 0; sniff_cell := 0;
x_envscan := 0x8b940; x_envscan_k := 0x8b94c; x_pnscan := 0x8ba04; x_pnscan_k := 0x8ba10;
stops_more := [0x34a6c; 0x36090; 0x53f50; 0x5a308; 0x5a31c; 0x5a330; 0x5fcc0; 0x5fd90; 0x6d2bc; 0x6e1c8; 0x6e358; 0x780b0; 0x6e4c8]
|}.
Definition TFIB_TEXT_LO : Z := 0x30a0c.
Definition TFIB_TEXT_N : nat := 108514.
Lemma TFIB_img_lo_val : img_lo TFIB = 0x10000.
Proof. reflexivity. Qed.
Lemma TFIB_img_hi_val : img_hi TFIB = 0x5fa000.
Proof. reflexivity. Qed.
