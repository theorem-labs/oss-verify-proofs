(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1q.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP02. From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x96a18 7%nat (build_table tfibsegs 0x95964 9%nat (build_table tfibsegs 0x8b24c 3%nat (build_table tfibsegs 0x81dc4 6%nat (build_table tfibsegs 0x758ac 70%nat (build_table tfibsegs 0x75248 90%nat (build_table tfibsegs 0x6e65c 8%nat (build_table tfibsegs 0x629d4 93%nat (build_table tfibsegs 0x60780 18%nat (build_table tfibsegs 0x5e3c4 44%nat (build_table tfibsegs 0x5e200 8%nat (build_table tfibsegs 0x5d3cc 14%nat (build_table tfibsegs 0x5c788 88%nat (build_table tfibsegs 0x5ba00 40%nat (build_table tfibsegs 0x5aaf0 6%nat (build_table tfibsegs 0x56d4c 16%nat (build_table tfibsegs 0x55bd0 324%nat (build_table tfibsegs 0x54d40 205%nat (build_table tfibsegs 0x48ca0 31%nat (build_table tfibsegs 0x3821c 1016%nat (build_table tfibsegs 0x36a38 96%nat (build_table tfibsegs 0x33d2c 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x74fa4 145%nat (build_table tfibsegs 0x748c4 169%nat (build_table tfibsegs 0x745dc 23%nat (build_table tfibsegs 0x72dd4 45%nat (build_table tfibsegs 0x722c8 150%nat (build_table tfibsegs 0x65d00 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x704cc 87%nat (build_table tfibsegs 0x7023c 100%nat (build_table tfibsegs 0x6e28c 75%nat (build_table tfibsegs 0x68928 131%nat (build_table tfibsegs 0x68288 111%nat (build_table tfibsegs 0x67d58 128%nat (build_table tfibsegs 0x67c3c 4%nat (build_table tfibsegs 0x674a8 2%nat (build_table tfibsegs 0x6655c 27%nat (build_table tfibsegs 0x62460 26%nat (build_table tfibsegs 0x61dc8 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6fa20 8%nat (build_table tfibsegs 0x8a910 139%nat (build_table tfibsegs 0x68b34 756%nat (build_table tfibsegs 0x65d7c 24%nat (build_table tfibsegs 0x704cc 87%nat (build_table tfibsegs 0x7023c 100%nat (build_table tfibsegs 0x6e28c 75%nat (build_table tfibsegs 0x68928 131%nat (build_table tfibsegs 0x68288 111%nat (build_table tfibsegs 0x67d58 128%nat (build_table tfibsegs 0x67c3c 4%nat (build_table tfibsegs 0x674a8 2%nat (build_table tfibsegs 0x6655c 27%nat (build_table tfibsegs 0x62460 26%nat (build_table tfibsegs 0x61dc8 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
