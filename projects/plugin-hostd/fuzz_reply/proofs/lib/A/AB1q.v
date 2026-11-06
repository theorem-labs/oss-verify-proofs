(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed, and its fuzz_reply.asan addresses relocated from cgif_file_fuzzer.asan (55 numerals; per-numeral report). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x982a0 7%nat (build_table tfibsegs 0x971ec 9%nat (build_table tfibsegs 0x8c9a8 3%nat (build_table tfibsegs 0x8180c 6%nat (build_table tfibsegs 0x752f4 70%nat (build_table tfibsegs 0x74c90 90%nat (build_table tfibsegs 0x6e0a4 8%nat (build_table tfibsegs 0x61e5c 93%nat (build_table tfibsegs 0x5fc08 18%nat (build_table tfibsegs 0x5d84c 44%nat (build_table tfibsegs 0x5d688 8%nat (build_table tfibsegs 0x5c7bc 14%nat (build_table tfibsegs 0x5bb78 88%nat (build_table tfibsegs 0x5adf0 40%nat (build_table tfibsegs 0x59ee0 6%nat (build_table tfibsegs 0x5613c 16%nat (build_table tfibsegs 0x54fc0 324%nat (build_table tfibsegs 0x53de8 206%nat (build_table tfibsegs 0x47958 31%nat (build_table tfibsegs 0x36278 1016%nat (build_table tfibsegs 0x34a94 96%nat (build_table tfibsegs 0x31b7c 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x749ec 145%nat (build_table tfibsegs 0x7430c 169%nat (build_table tfibsegs 0x74024 23%nat (build_table tfibsegs 0x7281c 45%nat (build_table tfibsegs 0x71d10 150%nat (build_table tfibsegs 0x65188 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6ff14 87%nat (build_table tfibsegs 0x6fc84 100%nat (build_table tfibsegs 0x6dcd4 75%nat (build_table tfibsegs 0x67db0 131%nat (build_table tfibsegs 0x67710 111%nat (build_table tfibsegs 0x671e0 128%nat (build_table tfibsegs 0x670c4 4%nat (build_table tfibsegs 0x66930 2%nat (build_table tfibsegs 0x659e4 27%nat (build_table tfibsegs 0x618e8 26%nat (build_table tfibsegs 0x61250 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6f468 8%nat (build_table tfibsegs 0x8c06c 139%nat (build_table tfibsegs 0x67fbc 756%nat (build_table tfibsegs 0x65204 24%nat (build_table tfibsegs 0x6ff14 87%nat (build_table tfibsegs 0x6fc84 100%nat (build_table tfibsegs 0x6dcd4 75%nat (build_table tfibsegs 0x67db0 131%nat (build_table tfibsegs 0x67710 111%nat (build_table tfibsegs 0x671e0 128%nat (build_table tfibsegs 0x670c4 4%nat (build_table tfibsegs 0x66930 2%nat (build_table tfibsegs 0x659e4 27%nat (build_table tfibsegs 0x618e8 26%nat (build_table tfibsegs 0x61250 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
