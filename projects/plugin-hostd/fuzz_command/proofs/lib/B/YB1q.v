(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed and its addresses moved to plugin-hostd/fuzz_command's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from this harness's lib/A/AB1q.v (the twin of cgif_file_fuzzer's lib/YB1q.v), with its module paths changed (lib/A to lib/B, image Asan to AsanUbsan) and its addresses moved to plugin-hostd/fuzz_command's ASan+UBSan build. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0xa07c8 7%nat (build_table tfibsegs 0x9f714 9%nat (build_table tfibsegs 0x94b60 3%nat (build_table tfibsegs 0x85a50 6%nat (build_table tfibsegs 0x79538 70%nat (build_table tfibsegs 0x78ed4 90%nat (build_table tfibsegs 0x722e8 8%nat (build_table tfibsegs 0x66660 93%nat (build_table tfibsegs 0x6440c 18%nat (build_table tfibsegs 0x62050 44%nat (build_table tfibsegs 0x61e8c 8%nat (build_table tfibsegs 0x61058 14%nat (build_table tfibsegs 0x60414 88%nat (build_table tfibsegs 0x5f68c 40%nat (build_table tfibsegs 0x5e77c 6%nat (build_table tfibsegs 0x5a9d8 16%nat (build_table tfibsegs 0x5985c 324%nat (build_table tfibsegs 0x589cc 205%nat (build_table tfibsegs 0x4b08c 31%nat (build_table tfibsegs 0x38a64 1016%nat (build_table tfibsegs 0x37280 96%nat (build_table tfibsegs 0x34574 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x78c30 145%nat (build_table tfibsegs 0x78550 169%nat (build_table tfibsegs 0x78268 23%nat (build_table tfibsegs 0x76a60 45%nat (build_table tfibsegs 0x75f54 150%nat (build_table tfibsegs 0x6998c 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x74158 87%nat (build_table tfibsegs 0x73ec8 100%nat (build_table tfibsegs 0x71f18 75%nat (build_table tfibsegs 0x6c5b4 131%nat (build_table tfibsegs 0x6bf14 111%nat (build_table tfibsegs 0x6b9e4 128%nat (build_table tfibsegs 0x6b8c8 4%nat (build_table tfibsegs 0x6b134 2%nat (build_table tfibsegs 0x6a1e8 27%nat (build_table tfibsegs 0x660ec 26%nat (build_table tfibsegs 0x65a54 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x736ac 8%nat (build_table tfibsegs 0x94224 139%nat (build_table tfibsegs 0x6c7c0 756%nat (build_table tfibsegs 0x69a08 24%nat (build_table tfibsegs 0x74158 87%nat (build_table tfibsegs 0x73ec8 100%nat (build_table tfibsegs 0x71f18 75%nat (build_table tfibsegs 0x6c5b4 131%nat (build_table tfibsegs 0x6bf14 111%nat (build_table tfibsegs 0x6b9e4 128%nat (build_table tfibsegs 0x6b8c8 4%nat (build_table tfibsegs 0x6b134 2%nat (build_table tfibsegs 0x6a1e8 27%nat (build_table tfibsegs 0x660ec 26%nat (build_table tfibsegs 0x65a54 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
