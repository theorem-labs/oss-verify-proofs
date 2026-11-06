(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x9c8ac 7%nat (build_table tfibsegs 0x9b7f8 9%nat (build_table tfibsegs 0x90a7c 3%nat (build_table tfibsegs 0x816ec 6%nat (build_table tfibsegs 0x751d4 70%nat (build_table tfibsegs 0x74b70 90%nat (build_table tfibsegs 0x6df84 8%nat (build_table tfibsegs 0x622fc 93%nat (build_table tfibsegs 0x600a8 18%nat (build_table tfibsegs 0x5dbd8 44%nat (build_table tfibsegs 0x5da14 8%nat (build_table tfibsegs 0x5cbe0 14%nat (build_table tfibsegs 0x5bf9c 88%nat (build_table tfibsegs 0x5b214 40%nat (build_table tfibsegs 0x5a304 6%nat (build_table tfibsegs 0x56310 16%nat (build_table tfibsegs 0x55194 324%nat (build_table tfibsegs 0x540c8 206%nat (build_table tfibsegs 0x47fa8 31%nat (build_table tfibsegs 0x36a24 1016%nat (build_table tfibsegs 0x35240 96%nat (build_table tfibsegs 0x32454 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x748cc 145%nat (build_table tfibsegs 0x741ec 169%nat (build_table tfibsegs 0x73f04 23%nat (build_table tfibsegs 0x726fc 45%nat (build_table tfibsegs 0x71bf0 150%nat (build_table tfibsegs 0x65628 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6fdf4 87%nat (build_table tfibsegs 0x6fb64 100%nat (build_table tfibsegs 0x6dbb4 75%nat (build_table tfibsegs 0x68250 131%nat (build_table tfibsegs 0x67bb0 111%nat (build_table tfibsegs 0x67680 128%nat (build_table tfibsegs 0x67564 4%nat (build_table tfibsegs 0x66dd0 2%nat (build_table tfibsegs 0x65e84 27%nat (build_table tfibsegs 0x61d88 26%nat (build_table tfibsegs 0x616f0 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6f348 8%nat (build_table tfibsegs 0x90140 139%nat (build_table tfibsegs 0x6845c 756%nat (build_table tfibsegs 0x656a4 24%nat (build_table tfibsegs 0x6fdf4 87%nat (build_table tfibsegs 0x6fb64 100%nat (build_table tfibsegs 0x6dbb4 75%nat (build_table tfibsegs 0x68250 131%nat (build_table tfibsegs 0x67bb0 111%nat (build_table tfibsegs 0x67680 128%nat (build_table tfibsegs 0x67564 4%nat (build_table tfibsegs 0x66dd0 2%nat (build_table tfibsegs 0x65e84 27%nat (build_table tfibsegs 0x61d88 26%nat (build_table tfibsegs 0x616f0 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
