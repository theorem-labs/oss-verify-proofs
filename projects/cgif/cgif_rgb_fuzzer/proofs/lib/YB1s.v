(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ03 YB1u YB1p.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition trbtbl_rtF_build : ctable := build_table trbsegs 0x64748 24%nat (build_table trbsegs 0x5ec48 84%nat (build_table trbsegs 0x35c00 323%nat (build_table trbsegs 0x31730 184%nat (trbtbl_rtA)))).
Definition trbtbl_rtF : ctable := Eval vm_compute in trbtbl_rtF_build.
Lemma trbtbl_rtF_eq : trbtbl_rtF = trbtbl_rtF_build.
Proof. vm_cast_no_check (@eq_refl ctable trbtbl_rtF). Qed.
Lemma trbtbl_rtF_ok : table_ok trbsegs trbtbl_rtF.
Proof. rewrite trbtbl_rtF_eq. unfold trbtbl_rtF_build. do 4 (apply build_table_ok; [cbv; discriminate|]). exact trbtbl_rtA_ok. Qed.
Definition trbtbl_rtG_build : ctable := build_table trbsegs 0x34aa8 123%nat (build_table trbsegs 0x33680 1194%nat (trbtbl_rtF)).
Definition trbtbl_rtG : ctable := Eval vm_compute in trbtbl_rtG_build.
Lemma trbtbl_rtG_eq : trbtbl_rtG = trbtbl_rtG_build.
Proof. vm_cast_no_check (@eq_refl ctable trbtbl_rtG). Qed.
Lemma trbtbl_rtG_ok : table_ok trbsegs trbtbl_rtG.
Proof. rewrite trbtbl_rtG_eq. unfold trbtbl_rtG_build. do 2 (apply build_table_ok; [cbv; discriminate|]). exact trbtbl_rtF_ok. Qed.
Definition trbtbl_rtK_build : ctable := build_table trbsegs 0x66798 26%nat (trbtbl_rtG).
Definition trbtbl_rtK : ctable := Eval vm_compute in trbtbl_rtK_build.
Lemma trbtbl_rtK_eq : trbtbl_rtK = trbtbl_rtK_build.
Proof. vm_cast_no_check (@eq_refl ctable trbtbl_rtK). Qed.
Lemma trbtbl_rtK_ok : table_ok trbsegs trbtbl_rtK.
Proof. rewrite trbtbl_rtK_eq. unfold trbtbl_rtK_build. do 1 (apply build_table_ok; [cbv; discriminate|]). exact trbtbl_rtG_ok. Qed.
Definition trbtbl_rtM_build : ctable := build_table trbsegs 0x60e70 9%nat (build_table trbsegs 0x64f28 30%nat (build_table trbsegs 0x6e348 41%nat (build_table trbsegs 0x530d0 50%nat (trbtbl_rtK)))).
Definition trbtbl_rtM : ctable := Eval vm_compute in trbtbl_rtM_build.
Lemma trbtbl_rtM_eq : trbtbl_rtM = trbtbl_rtM_build.
Proof. vm_cast_no_check (@eq_refl ctable trbtbl_rtM). Qed.
Lemma trbtbl_rtM_ok : table_ok trbsegs trbtbl_rtM.
Proof. rewrite trbtbl_rtM_eq. unfold trbtbl_rtM_build. do 4 (apply build_table_ok; [cbv; discriminate|]). exact trbtbl_rtK_ok. Qed.
