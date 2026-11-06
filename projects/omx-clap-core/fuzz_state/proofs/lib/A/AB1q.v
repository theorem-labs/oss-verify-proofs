(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the 0x53070 range is 206 words, through __interceptor_malloc's ret at 0x533a4; fuzz_state.asan has a third __wrap_ jump (__wrap_realloc at 0x53078) before __interceptor_free, so the cgif count 205 stopped one word short. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x9a6c8 7%nat (build_table tfibsegs 0x99614 9%nat (build_table tfibsegs 0x8c744 3%nat (build_table tfibsegs 0x8043c 6%nat (build_table tfibsegs 0x73f24 70%nat (build_table tfibsegs 0x738c0 90%nat (build_table tfibsegs 0x6ccd4 8%nat (build_table tfibsegs 0x6104c 93%nat (build_table tfibsegs 0x5edf8 18%nat (build_table tfibsegs 0x5ca3c 44%nat (build_table tfibsegs 0x5c878 8%nat (build_table tfibsegs 0x5ba44 14%nat (build_table tfibsegs 0x5ae00 88%nat (build_table tfibsegs 0x5a078 40%nat (build_table tfibsegs 0x59168 6%nat (build_table tfibsegs 0x553c4 16%nat (build_table tfibsegs 0x54248 324%nat (build_table tfibsegs 0x53070 206%nat (build_table tfibsegs 0x46fd0 31%nat (build_table tfibsegs 0x36594 1016%nat (build_table tfibsegs 0x34db0 96%nat (build_table tfibsegs 0x31e98 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x7361c 145%nat (build_table tfibsegs 0x72f3c 169%nat (build_table tfibsegs 0x72c54 23%nat (build_table tfibsegs 0x7144c 45%nat (build_table tfibsegs 0x70940 150%nat (build_table tfibsegs 0x64378 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6eb44 87%nat (build_table tfibsegs 0x6e8b4 100%nat (build_table tfibsegs 0x6c904 75%nat (build_table tfibsegs 0x66fa0 131%nat (build_table tfibsegs 0x66900 111%nat (build_table tfibsegs 0x663d0 128%nat (build_table tfibsegs 0x662b4 4%nat (build_table tfibsegs 0x65b20 2%nat (build_table tfibsegs 0x64bd4 27%nat (build_table tfibsegs 0x60ad8 26%nat (build_table tfibsegs 0x60440 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6e098 8%nat (build_table tfibsegs 0x8be08 139%nat (build_table tfibsegs 0x671ac 756%nat (build_table tfibsegs 0x643f4 24%nat (build_table tfibsegs 0x6eb44 87%nat (build_table tfibsegs 0x6e8b4 100%nat (build_table tfibsegs 0x6c904 75%nat (build_table tfibsegs 0x66fa0 131%nat (build_table tfibsegs 0x66900 111%nat (build_table tfibsegs 0x663d0 128%nat (build_table tfibsegs 0x662b4 4%nat (build_table tfibsegs 0x65b20 2%nat (build_table tfibsegs 0x64bd4 27%nat (build_table tfibsegs 0x60ad8 26%nat (build_table tfibsegs 0x60440 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
