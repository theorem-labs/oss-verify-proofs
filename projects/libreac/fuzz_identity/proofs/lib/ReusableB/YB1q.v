(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YB1q.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP02. From OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB Require Import YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x965a8 7%nat (build_table tfibsegs 0x954f4 9%nat (build_table tfibsegs 0x8addc 3%nat (build_table tfibsegs 0x7fc94 6%nat (build_table tfibsegs 0x7377c 70%nat (build_table tfibsegs 0x73118 90%nat (build_table tfibsegs 0x6c52c 8%nat (build_table tfibsegs 0x608a4 93%nat (build_table tfibsegs 0x5e650 18%nat (build_table tfibsegs 0x5c294 44%nat (build_table tfibsegs 0x5c0d0 8%nat (build_table tfibsegs 0x5b29c 14%nat (build_table tfibsegs 0x5a658 88%nat (build_table tfibsegs 0x598d0 40%nat (build_table tfibsegs 0x589c0 6%nat (build_table tfibsegs 0x54c1c 16%nat (build_table tfibsegs 0x53aa0 324%nat (build_table tfibsegs 0x52c10 205%nat (build_table tfibsegs 0x46b70 31%nat (build_table tfibsegs 0x360f8 1016%nat (build_table tfibsegs 0x34914 96%nat (build_table tfibsegs 0x31c08 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x72e74 145%nat (build_table tfibsegs 0x72794 169%nat (build_table tfibsegs 0x724ac 23%nat (build_table tfibsegs 0x70ca4 45%nat (build_table tfibsegs 0x70198 150%nat (build_table tfibsegs 0x63bd0 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6e39c 87%nat (build_table tfibsegs 0x6e10c 100%nat (build_table tfibsegs 0x6c15c 75%nat (build_table tfibsegs 0x667f8 131%nat (build_table tfibsegs 0x66158 111%nat (build_table tfibsegs 0x65c28 128%nat (build_table tfibsegs 0x65b0c 4%nat (build_table tfibsegs 0x65378 2%nat (build_table tfibsegs 0x6442c 27%nat (build_table tfibsegs 0x60330 26%nat (build_table tfibsegs 0x5fc98 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6d8f0 8%nat (build_table tfibsegs 0x8a4a0 139%nat (build_table tfibsegs 0x66a04 756%nat (build_table tfibsegs 0x63c4c 24%nat (build_table tfibsegs 0x6e39c 87%nat (build_table tfibsegs 0x6e10c 100%nat (build_table tfibsegs 0x6c15c 75%nat (build_table tfibsegs 0x667f8 131%nat (build_table tfibsegs 0x66158 111%nat (build_table tfibsegs 0x65c28 128%nat (build_table tfibsegs 0x65b0c 4%nat (build_table tfibsegs 0x65378 2%nat (build_table tfibsegs 0x6442c 27%nat (build_table tfibsegs 0x60330 26%nat (build_table tfibsegs 0x5fc98 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
