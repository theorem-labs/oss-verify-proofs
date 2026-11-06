(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x93e8c 7%nat (build_table tfibsegs 0x92dd8 9%nat (build_table tfibsegs 0x88660 3%nat (build_table tfibsegs 0x7f46c 6%nat (build_table tfibsegs 0x72f54 70%nat (build_table tfibsegs 0x728f0 90%nat (build_table tfibsegs 0x6bd04 8%nat (build_table tfibsegs 0x6007c 93%nat (build_table tfibsegs 0x5de28 18%nat (build_table tfibsegs 0x5ba6c 44%nat (build_table tfibsegs 0x5b8a8 8%nat (build_table tfibsegs 0x5aa74 14%nat (build_table tfibsegs 0x59e30 88%nat (build_table tfibsegs 0x590a8 40%nat (build_table tfibsegs 0x58198 6%nat (build_table tfibsegs 0x543f4 16%nat (build_table tfibsegs 0x53278 324%nat (build_table tfibsegs 0x523e8 205%nat (build_table tfibsegs 0x46348 31%nat (build_table tfibsegs 0x35630 1016%nat (build_table tfibsegs 0x33e4c 96%nat (build_table tfibsegs 0x31140 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x7264c 145%nat (build_table tfibsegs 0x71f6c 169%nat (build_table tfibsegs 0x71c84 23%nat (build_table tfibsegs 0x7047c 45%nat (build_table tfibsegs 0x6f970 150%nat (build_table tfibsegs 0x633a8 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6db74 87%nat (build_table tfibsegs 0x6d8e4 100%nat (build_table tfibsegs 0x6b934 75%nat (build_table tfibsegs 0x65fd0 131%nat (build_table tfibsegs 0x65930 111%nat (build_table tfibsegs 0x65400 128%nat (build_table tfibsegs 0x652e4 4%nat (build_table tfibsegs 0x64b50 2%nat (build_table tfibsegs 0x63c04 27%nat (build_table tfibsegs 0x5fb08 26%nat (build_table tfibsegs 0x5f470 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6d0c8 8%nat (build_table tfibsegs 0x87d24 139%nat (build_table tfibsegs 0x661dc 756%nat (build_table tfibsegs 0x63424 24%nat (build_table tfibsegs 0x6db74 87%nat (build_table tfibsegs 0x6d8e4 100%nat (build_table tfibsegs 0x6b934 75%nat (build_table tfibsegs 0x65fd0 131%nat (build_table tfibsegs 0x65930 111%nat (build_table tfibsegs 0x65400 128%nat (build_table tfibsegs 0x652e4 4%nat (build_table tfibsegs 0x64b50 2%nat (build_table tfibsegs 0x63c04 27%nat (build_table tfibsegs 0x5fb08 26%nat (build_table tfibsegs 0x5f470 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
