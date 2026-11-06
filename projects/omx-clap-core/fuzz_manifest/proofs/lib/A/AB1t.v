(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: relocated from cgif_file_fuzzer.asan to omx-clap-core fuzz_manifest.asan: 11 address literal(s) rewritten, module paths changed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AB1q.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtF_build : ctable := build_table tfibsegs 0x63df4 24%nat (build_table tfibsegs 0x5e2f4 84%nat (build_table tfibsegs 0x355d0 323%nat (build_table tfibsegs 0x3130c 184%nat (tfibtbl_rtA)))).
Definition tfibtbl_rtF : ctable := Eval vm_compute in tfibtbl_rtF_build.
Lemma tfibtbl_rtF_eq : tfibtbl_rtF = tfibtbl_rtF_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtF). Qed.
Lemma tfibtbl_rtF_ok : table_ok tfibsegs tfibtbl_rtF.
Proof. rewrite tfibtbl_rtF_eq. unfold tfibtbl_rtF_build. do 4 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
Definition tfibtbl_rtG_build : ctable := build_table tfibsegs 0x34478 123%nat (build_table tfibsegs 0x33050 1194%nat (tfibtbl_rtF)).
Definition tfibtbl_rtG : ctable := Eval vm_compute in tfibtbl_rtG_build.
Lemma tfibtbl_rtG_eq : tfibtbl_rtG = tfibtbl_rtG_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtG). Qed.
Lemma tfibtbl_rtG_ok : table_ok tfibsegs tfibtbl_rtG.
Proof. rewrite tfibtbl_rtG_eq. unfold tfibtbl_rtG_build. do 2 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtF_ok. Qed.
Definition tfibtbl_rtK_build : ctable := build_table tfibsegs 0x65e44 26%nat (tfibtbl_rtG).
Definition tfibtbl_rtK : ctable := Eval vm_compute in tfibtbl_rtK_build.
Lemma tfibtbl_rtK_eq : tfibtbl_rtK = tfibtbl_rtK_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtK). Qed.
Lemma tfibtbl_rtK_ok : table_ok tfibsegs tfibtbl_rtK.
Proof. rewrite tfibtbl_rtK_eq. unfold tfibtbl_rtK_build. do 1 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtG_ok. Qed.
Definition tfibtbl_rtM_build : ctable := build_table tfibsegs 0x6051c 9%nat (build_table tfibsegs 0x645d4 30%nat (build_table tfibsegs 0x6d9f4 41%nat (build_table tfibsegs 0x52ac4 50%nat (tfibtbl_rtK)))).
Definition tfibtbl_rtM : ctable := Eval vm_compute in tfibtbl_rtM_build.
Lemma tfibtbl_rtM_eq : tfibtbl_rtM = tfibtbl_rtM_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtM). Qed.
Lemma tfibtbl_rtM_ok : table_ok tfibsegs tfibtbl_rtM.
Proof. rewrite tfibtbl_rtM_eq. unfold tfibtbl_rtM_build. do 4 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtK_ok. Qed.
