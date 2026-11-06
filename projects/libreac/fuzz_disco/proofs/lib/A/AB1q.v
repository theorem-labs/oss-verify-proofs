(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed and its addresses moved to libreac/fuzz_disco's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x9b418 7%nat (build_table tfibsegs 0x9a364 9%nat (build_table tfibsegs 0x8fc4c 3%nat (build_table tfibsegs 0x80464 6%nat (build_table tfibsegs 0x73f4c 70%nat (build_table tfibsegs 0x738e8 90%nat (build_table tfibsegs 0x6ccfc 8%nat (build_table tfibsegs 0x61074 93%nat (build_table tfibsegs 0x5ee20 18%nat (build_table tfibsegs 0x5ca64 44%nat (build_table tfibsegs 0x5c8a0 8%nat (build_table tfibsegs 0x5ba6c 14%nat (build_table tfibsegs 0x5ae28 88%nat (build_table tfibsegs 0x5a0a0 40%nat (build_table tfibsegs 0x59190 6%nat (build_table tfibsegs 0x553ec 16%nat (build_table tfibsegs 0x54270 324%nat (build_table tfibsegs 0x533e0 205%nat (build_table tfibsegs 0x47340 31%nat (build_table tfibsegs 0x36584 1016%nat (build_table tfibsegs 0x34da0 96%nat (build_table tfibsegs 0x32094 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x73644 145%nat (build_table tfibsegs 0x72f64 169%nat (build_table tfibsegs 0x72c7c 23%nat (build_table tfibsegs 0x71474 45%nat (build_table tfibsegs 0x70968 150%nat (build_table tfibsegs 0x643a0 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6eb6c 87%nat (build_table tfibsegs 0x6e8dc 100%nat (build_table tfibsegs 0x6c92c 75%nat (build_table tfibsegs 0x66fc8 131%nat (build_table tfibsegs 0x66928 111%nat (build_table tfibsegs 0x663f8 128%nat (build_table tfibsegs 0x662dc 4%nat (build_table tfibsegs 0x65b48 2%nat (build_table tfibsegs 0x64bfc 27%nat (build_table tfibsegs 0x60b00 26%nat (build_table tfibsegs 0x60468 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6e0c0 8%nat (build_table tfibsegs 0x8f310 139%nat (build_table tfibsegs 0x671d4 756%nat (build_table tfibsegs 0x6441c 24%nat (build_table tfibsegs 0x6eb6c 87%nat (build_table tfibsegs 0x6e8dc 100%nat (build_table tfibsegs 0x6c92c 75%nat (build_table tfibsegs 0x66fc8 131%nat (build_table tfibsegs 0x66928 111%nat (build_table tfibsegs 0x663f8 128%nat (build_table tfibsegs 0x662dc 4%nat (build_table tfibsegs 0x65b48 2%nat (build_table tfibsegs 0x64bfc 27%nat (build_table tfibsegs 0x60b00 26%nat (build_table tfibsegs 0x60468 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
