(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed and its addresses moved to plugin-hostd/fuzz_command's ASan build. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0xa0c6c 7%nat (build_table tfibsegs 0x9fbb8 9%nat (build_table tfibsegs 0x95004 3%nat (build_table tfibsegs 0x85a04 6%nat (build_table tfibsegs 0x794ec 70%nat (build_table tfibsegs 0x78e88 90%nat (build_table tfibsegs 0x7229c 8%nat (build_table tfibsegs 0x66614 93%nat (build_table tfibsegs 0x643c0 18%nat (build_table tfibsegs 0x62004 44%nat (build_table tfibsegs 0x61e40 8%nat (build_table tfibsegs 0x6100c 14%nat (build_table tfibsegs 0x603c8 88%nat (build_table tfibsegs 0x5f640 40%nat (build_table tfibsegs 0x5e730 6%nat (build_table tfibsegs 0x5a98c 16%nat (build_table tfibsegs 0x59810 324%nat (build_table tfibsegs 0x58980 205%nat (build_table tfibsegs 0x4b040 31%nat (build_table tfibsegs 0x38a18 1016%nat (build_table tfibsegs 0x37234 96%nat (build_table tfibsegs 0x34528 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x78be4 145%nat (build_table tfibsegs 0x78504 169%nat (build_table tfibsegs 0x7821c 23%nat (build_table tfibsegs 0x76a14 45%nat (build_table tfibsegs 0x75f08 150%nat (build_table tfibsegs 0x69940 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x7410c 87%nat (build_table tfibsegs 0x73e7c 100%nat (build_table tfibsegs 0x71ecc 75%nat (build_table tfibsegs 0x6c568 131%nat (build_table tfibsegs 0x6bec8 111%nat (build_table tfibsegs 0x6b998 128%nat (build_table tfibsegs 0x6b87c 4%nat (build_table tfibsegs 0x6b0e8 2%nat (build_table tfibsegs 0x6a19c 27%nat (build_table tfibsegs 0x660a0 26%nat (build_table tfibsegs 0x65a08 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x73660 8%nat (build_table tfibsegs 0x946c8 139%nat (build_table tfibsegs 0x6c774 756%nat (build_table tfibsegs 0x699bc 24%nat (build_table tfibsegs 0x7410c 87%nat (build_table tfibsegs 0x73e7c 100%nat (build_table tfibsegs 0x71ecc 75%nat (build_table tfibsegs 0x6c568 131%nat (build_table tfibsegs 0x6bec8 111%nat (build_table tfibsegs 0x6b998 128%nat (build_table tfibsegs 0x6b87c 4%nat (build_table tfibsegs 0x6b0e8 2%nat (build_table tfibsegs 0x6a19c 27%nat (build_table tfibsegs 0x660a0 26%nat (build_table tfibsegs 0x65a08 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
