(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build; AB1v's tfibsegs is A/AWalkFw0.v's. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AB1q.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to reac-pw/fuzz_qdisc's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require Import AWalkFw0.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x908a0 7%nat (build_table tfibsegs 0x8f7ec 9%nat (build_table tfibsegs 0x850d8 3%nat (build_table tfibsegs 0x7dbac 6%nat (build_table tfibsegs 0x71694 70%nat (build_table tfibsegs 0x71030 90%nat (build_table tfibsegs 0x6a444 8%nat (build_table tfibsegs 0x5e7bc 93%nat (build_table tfibsegs 0x5c568 18%nat (build_table tfibsegs 0x5a1ac 44%nat (build_table tfibsegs 0x59fe8 8%nat (build_table tfibsegs 0x591b4 14%nat (build_table tfibsegs 0x58570 88%nat (build_table tfibsegs 0x577e8 40%nat (build_table tfibsegs 0x568d8 6%nat (build_table tfibsegs 0x52b34 16%nat (build_table tfibsegs 0x519b8 324%nat (build_table tfibsegs 0x50b28 205%nat (build_table tfibsegs 0x45164 31%nat (build_table tfibsegs 0x350bc 1016%nat (build_table tfibsegs 0x338d8 96%nat (build_table tfibsegs 0x30bcc 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x70d8c 145%nat (build_table tfibsegs 0x706ac 169%nat (build_table tfibsegs 0x703c4 23%nat (build_table tfibsegs 0x6ebbc 45%nat (build_table tfibsegs 0x6e0b0 150%nat (build_table tfibsegs 0x61ae8 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6c2b4 87%nat (build_table tfibsegs 0x6c024 100%nat (build_table tfibsegs 0x6a074 75%nat (build_table tfibsegs 0x64710 131%nat (build_table tfibsegs 0x64070 111%nat (build_table tfibsegs 0x63b40 128%nat (build_table tfibsegs 0x63a24 4%nat (build_table tfibsegs 0x63290 2%nat (build_table tfibsegs 0x62344 27%nat (build_table tfibsegs 0x5e248 26%nat (build_table tfibsegs 0x5dbb0 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6b808 8%nat (build_table tfibsegs 0x8479c 139%nat (build_table tfibsegs 0x6491c 756%nat (build_table tfibsegs 0x61b64 24%nat (build_table tfibsegs 0x6c2b4 87%nat (build_table tfibsegs 0x6c024 100%nat (build_table tfibsegs 0x6a074 75%nat (build_table tfibsegs 0x64710 131%nat (build_table tfibsegs 0x64070 111%nat (build_table tfibsegs 0x63b40 128%nat (build_table tfibsegs 0x63a24 4%nat (build_table tfibsegs 0x63290 2%nat (build_table tfibsegs 0x62344 27%nat (build_table tfibsegs 0x5e248 26%nat (build_table tfibsegs 0x5dbb0 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
