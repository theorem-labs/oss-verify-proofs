(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_ctrl's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x998b4 7%nat (build_table tfibsegs 0x98800 9%nat (build_table tfibsegs 0x8e0e8 3%nat (build_table tfibsegs 0x803fc 6%nat (build_table tfibsegs 0x73ee4 70%nat (build_table tfibsegs 0x73880 90%nat (build_table tfibsegs 0x6cc94 8%nat (build_table tfibsegs 0x6100c 93%nat (build_table tfibsegs 0x5edb8 18%nat (build_table tfibsegs 0x5c9fc 44%nat (build_table tfibsegs 0x5c838 8%nat (build_table tfibsegs 0x5ba04 14%nat (build_table tfibsegs 0x5adc0 88%nat (build_table tfibsegs 0x5a038 40%nat (build_table tfibsegs 0x59128 6%nat (build_table tfibsegs 0x55384 16%nat (build_table tfibsegs 0x54208 324%nat (build_table tfibsegs 0x53378 205%nat (build_table tfibsegs 0x472d8 31%nat (build_table tfibsegs 0x366c8 1016%nat (build_table tfibsegs 0x34ee4 96%nat (build_table tfibsegs 0x321d8 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x735dc 145%nat (build_table tfibsegs 0x72efc 169%nat (build_table tfibsegs 0x72c14 23%nat (build_table tfibsegs 0x7140c 45%nat (build_table tfibsegs 0x70900 150%nat (build_table tfibsegs 0x64338 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6eb04 87%nat (build_table tfibsegs 0x6e874 100%nat (build_table tfibsegs 0x6c8c4 75%nat (build_table tfibsegs 0x66f60 131%nat (build_table tfibsegs 0x668c0 111%nat (build_table tfibsegs 0x66390 128%nat (build_table tfibsegs 0x66274 4%nat (build_table tfibsegs 0x65ae0 2%nat (build_table tfibsegs 0x64b94 27%nat (build_table tfibsegs 0x60a98 26%nat (build_table tfibsegs 0x60400 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6e058 8%nat (build_table tfibsegs 0x8d7ac 139%nat (build_table tfibsegs 0x6716c 756%nat (build_table tfibsegs 0x643b4 24%nat (build_table tfibsegs 0x6eb04 87%nat (build_table tfibsegs 0x6e874 100%nat (build_table tfibsegs 0x6c8c4 75%nat (build_table tfibsegs 0x66f60 131%nat (build_table tfibsegs 0x668c0 111%nat (build_table tfibsegs 0x66390 128%nat (build_table tfibsegs 0x66274 4%nat (build_table tfibsegs 0x65ae0 2%nat (build_table tfibsegs 0x64b94 27%nat (build_table tfibsegs 0x60a98 26%nat (build_table tfibsegs 0x60400 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
