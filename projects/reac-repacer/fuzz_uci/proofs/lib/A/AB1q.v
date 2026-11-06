(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build. *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_grant/lib/A/AB1q.v (donor image sha256 c2c7559b29bd), with its module paths changed and its addresses moved to reac-repacer/fuzz_uci's ASan build. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x91ff8 7%nat (build_table tfibsegs 0x90f44 9%nat (build_table tfibsegs 0x86830 3%nat (build_table tfibsegs 0x7e808 6%nat (build_table tfibsegs 0x722f0 70%nat (build_table tfibsegs 0x71c8c 90%nat (build_table tfibsegs 0x6b0a0 8%nat (build_table tfibsegs 0x5f418 93%nat (build_table tfibsegs 0x5d1c4 18%nat (build_table tfibsegs 0x5ae08 44%nat (build_table tfibsegs 0x5ac44 8%nat (build_table tfibsegs 0x59e10 14%nat (build_table tfibsegs 0x591cc 88%nat (build_table tfibsegs 0x58444 40%nat (build_table tfibsegs 0x57534 6%nat (build_table tfibsegs 0x53790 16%nat (build_table tfibsegs 0x52614 324%nat (build_table tfibsegs 0x51784 205%nat (build_table tfibsegs 0x45924 31%nat (build_table tfibsegs 0x352c8 1016%nat (build_table tfibsegs 0x33ae4 96%nat (build_table tfibsegs 0x30dd8 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x719e8 145%nat (build_table tfibsegs 0x71308 169%nat (build_table tfibsegs 0x71020 23%nat (build_table tfibsegs 0x6f818 45%nat (build_table tfibsegs 0x6ed0c 150%nat (build_table tfibsegs 0x62744 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6cf10 87%nat (build_table tfibsegs 0x6cc80 100%nat (build_table tfibsegs 0x6acd0 75%nat (build_table tfibsegs 0x6536c 131%nat (build_table tfibsegs 0x64ccc 111%nat (build_table tfibsegs 0x6479c 128%nat (build_table tfibsegs 0x64680 4%nat (build_table tfibsegs 0x63eec 2%nat (build_table tfibsegs 0x62fa0 27%nat (build_table tfibsegs 0x5eea4 26%nat (build_table tfibsegs 0x5e80c 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6c464 8%nat (build_table tfibsegs 0x85ef4 139%nat (build_table tfibsegs 0x65578 756%nat (build_table tfibsegs 0x627c0 24%nat (build_table tfibsegs 0x6cf10 87%nat (build_table tfibsegs 0x6cc80 100%nat (build_table tfibsegs 0x6acd0 75%nat (build_table tfibsegs 0x6536c 131%nat (build_table tfibsegs 0x64ccc 111%nat (build_table tfibsegs 0x6479c 128%nat (build_table tfibsegs 0x64680 4%nat (build_table tfibsegs 0x63eec 2%nat (build_table tfibsegs 0x62fa0 27%nat (build_table tfibsegs 0x5eea4 26%nat (build_table tfibsegs 0x5e80c 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
