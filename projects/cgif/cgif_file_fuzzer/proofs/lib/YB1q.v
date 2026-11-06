(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP02 YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x991b0 7%nat (build_table tfibsegs 0x980fc 9%nat (build_table tfibsegs 0x8d56c 3%nat (build_table tfibsegs 0x7f9e0 6%nat (build_table tfibsegs 0x734c8 70%nat (build_table tfibsegs 0x72e64 90%nat (build_table tfibsegs 0x6c278 8%nat (build_table tfibsegs 0x605f0 93%nat (build_table tfibsegs 0x5e39c 18%nat (build_table tfibsegs 0x5bfe0 44%nat (build_table tfibsegs 0x5be1c 8%nat (build_table tfibsegs 0x5afe8 14%nat (build_table tfibsegs 0x5a3a4 88%nat (build_table tfibsegs 0x5961c 40%nat (build_table tfibsegs 0x5870c 6%nat (build_table tfibsegs 0x54968 16%nat (build_table tfibsegs 0x537ec 324%nat (build_table tfibsegs 0x5295c 205%nat (build_table tfibsegs 0x462a4 31%nat (build_table tfibsegs 0x359e4 1016%nat (build_table tfibsegs 0x34200 96%nat (build_table tfibsegs 0x314f4 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x72bc0 145%nat (build_table tfibsegs 0x724e0 169%nat (build_table tfibsegs 0x721f8 23%nat (build_table tfibsegs 0x709f0 45%nat (build_table tfibsegs 0x6fee4 150%nat (build_table tfibsegs 0x6391c 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6e0e8 87%nat (build_table tfibsegs 0x6de58 100%nat (build_table tfibsegs 0x6bea8 75%nat (build_table tfibsegs 0x66544 131%nat (build_table tfibsegs 0x65ea4 111%nat (build_table tfibsegs 0x65974 128%nat (build_table tfibsegs 0x65858 4%nat (build_table tfibsegs 0x650c4 2%nat (build_table tfibsegs 0x64178 27%nat (build_table tfibsegs 0x6007c 26%nat (build_table tfibsegs 0x5f9e4 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6d63c 8%nat (build_table tfibsegs 0x8cc30 139%nat (build_table tfibsegs 0x66750 756%nat (build_table tfibsegs 0x63998 24%nat (build_table tfibsegs 0x6e0e8 87%nat (build_table tfibsegs 0x6de58 100%nat (build_table tfibsegs 0x6bea8 75%nat (build_table tfibsegs 0x66544 131%nat (build_table tfibsegs 0x65ea4 111%nat (build_table tfibsegs 0x65974 128%nat (build_table tfibsegs 0x65858 4%nat (build_table tfibsegs 0x650c4 2%nat (build_table tfibsegs 0x64178 27%nat (build_table tfibsegs 0x6007c 26%nat (build_table tfibsegs 0x5f9e4 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
