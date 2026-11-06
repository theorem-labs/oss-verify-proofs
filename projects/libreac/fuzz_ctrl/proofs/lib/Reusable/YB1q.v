(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1q.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_ctrl's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YP02 YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x9a6d8 7%nat (build_table tfibsegs 0x99624 9%nat (build_table tfibsegs 0x8ef0c 3%nat (build_table tfibsegs 0x80538 6%nat (build_table tfibsegs 0x74020 70%nat (build_table tfibsegs 0x739bc 90%nat (build_table tfibsegs 0x6cdd0 8%nat (build_table tfibsegs 0x61148 93%nat (build_table tfibsegs 0x5eef4 18%nat (build_table tfibsegs 0x5cb38 44%nat (build_table tfibsegs 0x5c974 8%nat (build_table tfibsegs 0x5bb40 14%nat (build_table tfibsegs 0x5aefc 88%nat (build_table tfibsegs 0x5a174 40%nat (build_table tfibsegs 0x59264 6%nat (build_table tfibsegs 0x554c0 16%nat (build_table tfibsegs 0x54344 324%nat (build_table tfibsegs 0x534b4 205%nat (build_table tfibsegs 0x47414 31%nat (build_table tfibsegs 0x36804 1016%nat (build_table tfibsegs 0x35020 96%nat (build_table tfibsegs 0x32314 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x73718 145%nat (build_table tfibsegs 0x73038 169%nat (build_table tfibsegs 0x72d50 23%nat (build_table tfibsegs 0x71548 45%nat (build_table tfibsegs 0x70a3c 150%nat (build_table tfibsegs 0x64474 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6ec40 87%nat (build_table tfibsegs 0x6e9b0 100%nat (build_table tfibsegs 0x6ca00 75%nat (build_table tfibsegs 0x6709c 131%nat (build_table tfibsegs 0x669fc 111%nat (build_table tfibsegs 0x664cc 128%nat (build_table tfibsegs 0x663b0 4%nat (build_table tfibsegs 0x65c1c 2%nat (build_table tfibsegs 0x64cd0 27%nat (build_table tfibsegs 0x60bd4 26%nat (build_table tfibsegs 0x6053c 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6e194 8%nat (build_table tfibsegs 0x8e5d0 139%nat (build_table tfibsegs 0x672a8 756%nat (build_table tfibsegs 0x644f0 24%nat (build_table tfibsegs 0x6ec40 87%nat (build_table tfibsegs 0x6e9b0 100%nat (build_table tfibsegs 0x6ca00 75%nat (build_table tfibsegs 0x6709c 131%nat (build_table tfibsegs 0x669fc 111%nat (build_table tfibsegs 0x664cc 128%nat (build_table tfibsegs 0x663b0 4%nat (build_table tfibsegs 0x65c1c 2%nat (build_table tfibsegs 0x64cd0 27%nat (build_table tfibsegs 0x60bd4 26%nat (build_table tfibsegs 0x6053c 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
