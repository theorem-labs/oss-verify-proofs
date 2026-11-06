(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AB1q.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x962bc 7%nat (build_table tfibsegs 0x95208 9%nat (build_table tfibsegs 0x8aaf0 3%nat (build_table tfibsegs 0x7fc2c 6%nat (build_table tfibsegs 0x73714 70%nat (build_table tfibsegs 0x730b0 90%nat (build_table tfibsegs 0x6c4c4 8%nat (build_table tfibsegs 0x6083c 93%nat (build_table tfibsegs 0x5e5e8 18%nat (build_table tfibsegs 0x5c22c 44%nat (build_table tfibsegs 0x5c068 8%nat (build_table tfibsegs 0x5b234 14%nat (build_table tfibsegs 0x5a5f0 88%nat (build_table tfibsegs 0x59868 40%nat (build_table tfibsegs 0x58958 6%nat (build_table tfibsegs 0x54bb4 16%nat (build_table tfibsegs 0x53a38 324%nat (build_table tfibsegs 0x52ba8 205%nat (build_table tfibsegs 0x46b08 31%nat (build_table tfibsegs 0x36090 1016%nat (build_table tfibsegs 0x348ac 96%nat (build_table tfibsegs 0x31ba0 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x72e0c 145%nat (build_table tfibsegs 0x7272c 169%nat (build_table tfibsegs 0x72444 23%nat (build_table tfibsegs 0x70c3c 45%nat (build_table tfibsegs 0x70130 150%nat (build_table tfibsegs 0x63b68 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6e334 87%nat (build_table tfibsegs 0x6e0a4 100%nat (build_table tfibsegs 0x6c0f4 75%nat (build_table tfibsegs 0x66790 131%nat (build_table tfibsegs 0x660f0 111%nat (build_table tfibsegs 0x65bc0 128%nat (build_table tfibsegs 0x65aa4 4%nat (build_table tfibsegs 0x65310 2%nat (build_table tfibsegs 0x643c4 27%nat (build_table tfibsegs 0x602c8 26%nat (build_table tfibsegs 0x5fc30 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6d888 8%nat (build_table tfibsegs 0x8a1b4 139%nat (build_table tfibsegs 0x6699c 756%nat (build_table tfibsegs 0x63be4 24%nat (build_table tfibsegs 0x6e334 87%nat (build_table tfibsegs 0x6e0a4 100%nat (build_table tfibsegs 0x6c0f4 75%nat (build_table tfibsegs 0x66790 131%nat (build_table tfibsegs 0x660f0 111%nat (build_table tfibsegs 0x65bc0 128%nat (build_table tfibsegs 0x65aa4 4%nat (build_table tfibsegs 0x65310 2%nat (build_table tfibsegs 0x643c4 27%nat (build_table tfibsegs 0x602c8 26%nat (build_table tfibsegs 0x5fc30 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
