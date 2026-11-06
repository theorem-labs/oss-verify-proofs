(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1q.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP02. From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x98538 7%nat (build_table tfibsegs 0x97484 9%nat (build_table tfibsegs 0x8cd6c 3%nat (build_table tfibsegs 0x7ff5c 6%nat (build_table tfibsegs 0x73a44 70%nat (build_table tfibsegs 0x733e0 90%nat (build_table tfibsegs 0x6c7f4 8%nat (build_table tfibsegs 0x60b6c 93%nat (build_table tfibsegs 0x5e918 18%nat (build_table tfibsegs 0x5c55c 44%nat (build_table tfibsegs 0x5c398 8%nat (build_table tfibsegs 0x5b564 14%nat (build_table tfibsegs 0x5a920 88%nat (build_table tfibsegs 0x59b98 40%nat (build_table tfibsegs 0x58c88 6%nat (build_table tfibsegs 0x54ee4 16%nat (build_table tfibsegs 0x53d68 324%nat (build_table tfibsegs 0x52ed8 205%nat (build_table tfibsegs 0x46e38 31%nat (build_table tfibsegs 0x3605c 1016%nat (build_table tfibsegs 0x34878 96%nat (build_table tfibsegs 0x31b6c 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x7313c 145%nat (build_table tfibsegs 0x72a5c 169%nat (build_table tfibsegs 0x72774 23%nat (build_table tfibsegs 0x70f6c 45%nat (build_table tfibsegs 0x70460 150%nat (build_table tfibsegs 0x63e98 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6e664 87%nat (build_table tfibsegs 0x6e3d4 100%nat (build_table tfibsegs 0x6c424 75%nat (build_table tfibsegs 0x66ac0 131%nat (build_table tfibsegs 0x66420 111%nat (build_table tfibsegs 0x65ef0 128%nat (build_table tfibsegs 0x65dd4 4%nat (build_table tfibsegs 0x65640 2%nat (build_table tfibsegs 0x646f4 27%nat (build_table tfibsegs 0x605f8 26%nat (build_table tfibsegs 0x5ff60 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6dbb8 8%nat (build_table tfibsegs 0x8c430 139%nat (build_table tfibsegs 0x66ccc 756%nat (build_table tfibsegs 0x63f14 24%nat (build_table tfibsegs 0x6e664 87%nat (build_table tfibsegs 0x6e3d4 100%nat (build_table tfibsegs 0x6c424 75%nat (build_table tfibsegs 0x66ac0 131%nat (build_table tfibsegs 0x66420 111%nat (build_table tfibsegs 0x65ef0 128%nat (build_table tfibsegs 0x65dd4 4%nat (build_table tfibsegs 0x65640 2%nat (build_table tfibsegs 0x646f4 27%nat (build_table tfibsegs 0x605f8 26%nat (build_table tfibsegs 0x5ff60 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
