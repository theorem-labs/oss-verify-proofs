(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ03 YB0z YB0u.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tratbl_rtF_build : ctable := build_table trasegs 0x64484 24%nat (build_table trasegs 0x5e984 84%nat (build_table trasegs 0x35ab0 323%nat (build_table trasegs 0x315e0 184%nat (tratbl_rtA)))).
Definition tratbl_rtF : ctable := Eval vm_compute in tratbl_rtF_build.
Lemma tratbl_rtF_eq : tratbl_rtF = tratbl_rtF_build.
Proof. vm_cast_no_check (@eq_refl ctable tratbl_rtF). Qed.
Lemma tratbl_rtF_ok : table_ok trasegs tratbl_rtF.
Proof. rewrite tratbl_rtF_eq. unfold tratbl_rtF_build. do 4 (apply build_table_ok; [cbv; discriminate|]). exact tratbl_rtA_ok. Qed.
Definition tratbl_rtG_build : ctable := build_table trasegs 0x34958 123%nat (build_table trasegs 0x33530 1194%nat (tratbl_rtF)).
Definition tratbl_rtG : ctable := Eval vm_compute in tratbl_rtG_build.
Lemma tratbl_rtG_eq : tratbl_rtG = tratbl_rtG_build.
Proof. vm_cast_no_check (@eq_refl ctable tratbl_rtG). Qed.
Lemma tratbl_rtG_ok : table_ok trasegs tratbl_rtG.
Proof. rewrite tratbl_rtG_eq. unfold tratbl_rtG_build. do 2 (apply build_table_ok; [cbv; discriminate|]). exact tratbl_rtF_ok. Qed.
Definition tratbl_rtK_build : ctable := build_table trasegs 0x664d4 26%nat (tratbl_rtG).
Definition tratbl_rtK : ctable := Eval vm_compute in tratbl_rtK_build.
Lemma tratbl_rtK_eq : tratbl_rtK = tratbl_rtK_build.
Proof. vm_cast_no_check (@eq_refl ctable tratbl_rtK). Qed.
Lemma tratbl_rtK_ok : table_ok trasegs tratbl_rtK.
Proof. rewrite tratbl_rtK_eq. unfold tratbl_rtK_build. do 1 (apply build_table_ok; [cbv; discriminate|]). exact tratbl_rtG_ok. Qed.
Definition tratbl_rtM_build : ctable := build_table trasegs 0x60bac 9%nat (build_table trasegs 0x64c64 30%nat (build_table trasegs 0x6e084 41%nat (build_table trasegs 0x52e0c 50%nat (tratbl_rtK)))).
Definition tratbl_rtM : ctable := Eval vm_compute in tratbl_rtM_build.
Lemma tratbl_rtM_eq : tratbl_rtM = tratbl_rtM_build.
Proof. vm_cast_no_check (@eq_refl ctable tratbl_rtM). Qed.
Lemma tratbl_rtM_ok : table_ok trasegs tratbl_rtM.
Proof. rewrite tratbl_rtM_eq. unfold tratbl_rtM_build. do 4 (apply build_table_ok; [cbv; discriminate|]). exact tratbl_rtK_ok. Qed.
