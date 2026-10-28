(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x98f3c 7%nat (build_table tfibsegs 0x97e88 9%nat (build_table tfibsegs 0x8d2f8 3%nat (build_table tfibsegs 0x7f9b0 6%nat (build_table tfibsegs 0x73498 70%nat (build_table tfibsegs 0x72e34 90%nat (build_table tfibsegs 0x6c248 8%nat (build_table tfibsegs 0x605c0 93%nat (build_table tfibsegs 0x5e36c 18%nat (build_table tfibsegs 0x5bfb0 44%nat (build_table tfibsegs 0x5bdec 8%nat (build_table tfibsegs 0x5afb8 14%nat (build_table tfibsegs 0x5a374 88%nat (build_table tfibsegs 0x595ec 40%nat (build_table tfibsegs 0x586dc 6%nat (build_table tfibsegs 0x54938 16%nat (build_table tfibsegs 0x537bc 324%nat (build_table tfibsegs 0x5292c 205%nat (build_table tfibsegs 0x46274 31%nat (build_table tfibsegs 0x359b4 1016%nat (build_table tfibsegs 0x341d0 96%nat (build_table tfibsegs 0x314c4 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x72b90 145%nat (build_table tfibsegs 0x724b0 169%nat (build_table tfibsegs 0x721c8 23%nat (build_table tfibsegs 0x709c0 45%nat (build_table tfibsegs 0x6feb4 150%nat (build_table tfibsegs 0x638ec 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6e0b8 87%nat (build_table tfibsegs 0x6de28 100%nat (build_table tfibsegs 0x6be78 75%nat (build_table tfibsegs 0x66514 131%nat (build_table tfibsegs 0x65e74 111%nat (build_table tfibsegs 0x65944 128%nat (build_table tfibsegs 0x65828 4%nat (build_table tfibsegs 0x65094 2%nat (build_table tfibsegs 0x64148 27%nat (build_table tfibsegs 0x6004c 26%nat (build_table tfibsegs 0x5f9b4 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6d60c 8%nat (build_table tfibsegs 0x8c9bc 139%nat (build_table tfibsegs 0x66720 756%nat (build_table tfibsegs 0x63968 24%nat (build_table tfibsegs 0x6e0b8 87%nat (build_table tfibsegs 0x6de28 100%nat (build_table tfibsegs 0x6be78 75%nat (build_table tfibsegs 0x66514 131%nat (build_table tfibsegs 0x65e74 111%nat (build_table tfibsegs 0x65944 128%nat (build_table tfibsegs 0x65828 4%nat (build_table tfibsegs 0x65094 2%nat (build_table tfibsegs 0x64148 27%nat (build_table tfibsegs 0x6004c 26%nat (build_table tfibsegs 0x5f9b4 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
