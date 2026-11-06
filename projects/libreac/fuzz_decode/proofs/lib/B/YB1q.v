(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1q.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_decode's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP02. From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x942c0 7%nat (build_table tfibsegs 0x9320c 9%nat (build_table tfibsegs 0x88af4 3%nat (build_table tfibsegs 0x7f5d0 6%nat (build_table tfibsegs 0x730b8 70%nat (build_table tfibsegs 0x72a54 90%nat (build_table tfibsegs 0x6be68 8%nat (build_table tfibsegs 0x601e0 93%nat (build_table tfibsegs 0x5df8c 18%nat (build_table tfibsegs 0x5babc 44%nat (build_table tfibsegs 0x5b8f8 8%nat (build_table tfibsegs 0x5aac4 14%nat (build_table tfibsegs 0x59e80 88%nat (build_table tfibsegs 0x590f8 40%nat (build_table tfibsegs 0x581e8 6%nat (build_table tfibsegs 0x541f4 16%nat (build_table tfibsegs 0x53078 324%nat (build_table tfibsegs 0x51fac 206%nat (build_table tfibsegs 0x45f0c 31%nat (build_table tfibsegs 0x3580c 1016%nat (build_table tfibsegs 0x34028 96%nat (build_table tfibsegs 0x3123c 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x727b0 145%nat (build_table tfibsegs 0x720d0 169%nat (build_table tfibsegs 0x71de8 23%nat (build_table tfibsegs 0x705e0 45%nat (build_table tfibsegs 0x6fad4 150%nat (build_table tfibsegs 0x6350c 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6dcd8 87%nat (build_table tfibsegs 0x6da48 100%nat (build_table tfibsegs 0x6ba98 75%nat (build_table tfibsegs 0x66134 131%nat (build_table tfibsegs 0x65a94 111%nat (build_table tfibsegs 0x65564 128%nat (build_table tfibsegs 0x65448 4%nat (build_table tfibsegs 0x64cb4 2%nat (build_table tfibsegs 0x63d68 27%nat (build_table tfibsegs 0x5fc6c 26%nat (build_table tfibsegs 0x5f5d4 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6d22c 8%nat (build_table tfibsegs 0x881b8 139%nat (build_table tfibsegs 0x66340 756%nat (build_table tfibsegs 0x63588 24%nat (build_table tfibsegs 0x6dcd8 87%nat (build_table tfibsegs 0x6da48 100%nat (build_table tfibsegs 0x6ba98 75%nat (build_table tfibsegs 0x66134 131%nat (build_table tfibsegs 0x65a94 111%nat (build_table tfibsegs 0x65564 128%nat (build_table tfibsegs 0x65448 4%nat (build_table tfibsegs 0x64cb4 2%nat (build_table tfibsegs 0x63d68 27%nat (build_table tfibsegs 0x5fc6c 26%nat (build_table tfibsegs 0x5f5d4 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
