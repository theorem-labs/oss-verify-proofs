(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1q.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/B/YB1q.v at 4f87de75d67 (donor image sha256 fde52226dc48), with its module paths changed and its addresses moved to reac-repacer/fuzz_wire's ASan+UBSan build. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YP02. From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x93850 7%nat (build_table tfibsegs 0x9279c 9%nat (build_table tfibsegs 0x88084 3%nat (build_table tfibsegs 0x7f118 6%nat (build_table tfibsegs 0x72c00 70%nat (build_table tfibsegs 0x7259c 90%nat (build_table tfibsegs 0x6b9b0 8%nat (build_table tfibsegs 0x5fd28 93%nat (build_table tfibsegs 0x5dad4 18%nat (build_table tfibsegs 0x5b718 44%nat (build_table tfibsegs 0x5b554 8%nat (build_table tfibsegs 0x5a720 14%nat (build_table tfibsegs 0x59adc 88%nat (build_table tfibsegs 0x58d54 40%nat (build_table tfibsegs 0x57e44 6%nat (build_table tfibsegs 0x540a0 16%nat (build_table tfibsegs 0x52f24 324%nat (build_table tfibsegs 0x52094 205%nat (build_table tfibsegs 0x45ec4 31%nat (build_table tfibsegs 0x35634 1016%nat (build_table tfibsegs 0x33e50 96%nat (build_table tfibsegs 0x31144 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x722f8 145%nat (build_table tfibsegs 0x71c18 169%nat (build_table tfibsegs 0x71930 23%nat (build_table tfibsegs 0x70128 45%nat (build_table tfibsegs 0x6f61c 150%nat (build_table tfibsegs 0x63054 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6d820 87%nat (build_table tfibsegs 0x6d590 100%nat (build_table tfibsegs 0x6b5e0 75%nat (build_table tfibsegs 0x65c7c 131%nat (build_table tfibsegs 0x655dc 111%nat (build_table tfibsegs 0x650ac 128%nat (build_table tfibsegs 0x64f90 4%nat (build_table tfibsegs 0x647fc 2%nat (build_table tfibsegs 0x638b0 27%nat (build_table tfibsegs 0x5f7b4 26%nat (build_table tfibsegs 0x5f11c 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6cd74 8%nat (build_table tfibsegs 0x87748 139%nat (build_table tfibsegs 0x65e88 756%nat (build_table tfibsegs 0x630d0 24%nat (build_table tfibsegs 0x6d820 87%nat (build_table tfibsegs 0x6d590 100%nat (build_table tfibsegs 0x6b5e0 75%nat (build_table tfibsegs 0x65c7c 131%nat (build_table tfibsegs 0x655dc 111%nat (build_table tfibsegs 0x650ac 128%nat (build_table tfibsegs 0x64f90 4%nat (build_table tfibsegs 0x647fc 2%nat (build_table tfibsegs 0x638b0 27%nat (build_table tfibsegs 0x5f7b4 26%nat (build_table tfibsegs 0x5f11c 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
