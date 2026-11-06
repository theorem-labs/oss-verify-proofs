(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x966e4 7%nat (build_table tfibsegs 0x95630 9%nat (build_table tfibsegs 0x8af18 3%nat (build_table tfibsegs 0x81d98 6%nat (build_table tfibsegs 0x75880 70%nat (build_table tfibsegs 0x7521c 90%nat (build_table tfibsegs 0x6e630 8%nat (build_table tfibsegs 0x629a8 93%nat (build_table tfibsegs 0x60754 18%nat (build_table tfibsegs 0x5e398 44%nat (build_table tfibsegs 0x5e1d4 8%nat (build_table tfibsegs 0x5d3a0 14%nat (build_table tfibsegs 0x5c75c 88%nat (build_table tfibsegs 0x5b9d4 40%nat (build_table tfibsegs 0x5aac4 6%nat (build_table tfibsegs 0x56d20 16%nat (build_table tfibsegs 0x55ba4 324%nat (build_table tfibsegs 0x54d14 205%nat (build_table tfibsegs 0x48c74 31%nat (build_table tfibsegs 0x381f0 1016%nat (build_table tfibsegs 0x36a0c 96%nat (build_table tfibsegs 0x33d00 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x74f78 145%nat (build_table tfibsegs 0x74898 169%nat (build_table tfibsegs 0x745b0 23%nat (build_table tfibsegs 0x72da8 45%nat (build_table tfibsegs 0x7229c 150%nat (build_table tfibsegs 0x65cd4 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x704a0 87%nat (build_table tfibsegs 0x70210 100%nat (build_table tfibsegs 0x6e260 75%nat (build_table tfibsegs 0x688fc 131%nat (build_table tfibsegs 0x6825c 111%nat (build_table tfibsegs 0x67d2c 128%nat (build_table tfibsegs 0x67c10 4%nat (build_table tfibsegs 0x6747c 2%nat (build_table tfibsegs 0x66530 27%nat (build_table tfibsegs 0x62434 26%nat (build_table tfibsegs 0x61d9c 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6f9f4 8%nat (build_table tfibsegs 0x8a5dc 139%nat (build_table tfibsegs 0x68b08 756%nat (build_table tfibsegs 0x65d50 24%nat (build_table tfibsegs 0x704a0 87%nat (build_table tfibsegs 0x70210 100%nat (build_table tfibsegs 0x6e260 75%nat (build_table tfibsegs 0x688fc 131%nat (build_table tfibsegs 0x6825c 111%nat (build_table tfibsegs 0x67d2c 128%nat (build_table tfibsegs 0x67c10 4%nat (build_table tfibsegs 0x6747c 2%nat (build_table tfibsegs 0x66530 27%nat (build_table tfibsegs 0x62434 26%nat (build_table tfibsegs 0x61d9c 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
