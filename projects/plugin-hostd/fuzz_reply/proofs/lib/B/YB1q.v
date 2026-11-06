(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1q.v, with its module paths changed, and its fuzz_reply.asan-ubsan addresses relocated from cgif_file_fuzzer.asan-ubsan (55 numerals; per-numeral report). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x98820 7%nat (build_table tfibsegs 0x9776c 9%nat (build_table tfibsegs 0x8cf28 3%nat (build_table tfibsegs 0x81864 6%nat (build_table tfibsegs 0x7534c 70%nat (build_table tfibsegs 0x74ce8 90%nat (build_table tfibsegs 0x6e0fc 8%nat (build_table tfibsegs 0x61eb4 93%nat (build_table tfibsegs 0x5fc60 18%nat (build_table tfibsegs 0x5d8a4 44%nat (build_table tfibsegs 0x5d6e0 8%nat (build_table tfibsegs 0x5c814 14%nat (build_table tfibsegs 0x5bbd0 88%nat (build_table tfibsegs 0x5ae48 40%nat (build_table tfibsegs 0x59f38 6%nat (build_table tfibsegs 0x56194 16%nat (build_table tfibsegs 0x55018 324%nat (build_table tfibsegs 0x53e40 206%nat (build_table tfibsegs 0x479b0 31%nat (build_table tfibsegs 0x362d0 1016%nat (build_table tfibsegs 0x34aec 96%nat (build_table tfibsegs 0x31bd4 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x74a44 145%nat (build_table tfibsegs 0x74364 169%nat (build_table tfibsegs 0x7407c 23%nat (build_table tfibsegs 0x72874 45%nat (build_table tfibsegs 0x71d68 150%nat (build_table tfibsegs 0x651e0 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6ff6c 87%nat (build_table tfibsegs 0x6fcdc 100%nat (build_table tfibsegs 0x6dd2c 75%nat (build_table tfibsegs 0x67e08 131%nat (build_table tfibsegs 0x67768 111%nat (build_table tfibsegs 0x67238 128%nat (build_table tfibsegs 0x6711c 4%nat (build_table tfibsegs 0x66988 2%nat (build_table tfibsegs 0x65a3c 27%nat (build_table tfibsegs 0x61940 26%nat (build_table tfibsegs 0x612a8 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6f4c0 8%nat (build_table tfibsegs 0x8c5ec 139%nat (build_table tfibsegs 0x68014 756%nat (build_table tfibsegs 0x6525c 24%nat (build_table tfibsegs 0x6ff6c 87%nat (build_table tfibsegs 0x6fcdc 100%nat (build_table tfibsegs 0x6dd2c 75%nat (build_table tfibsegs 0x67e08 131%nat (build_table tfibsegs 0x67768 111%nat (build_table tfibsegs 0x67238 128%nat (build_table tfibsegs 0x6711c 4%nat (build_table tfibsegs 0x66988 2%nat (build_table tfibsegs 0x65a3c 27%nat (build_table tfibsegs 0x61940 26%nat (build_table tfibsegs 0x612a8 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
