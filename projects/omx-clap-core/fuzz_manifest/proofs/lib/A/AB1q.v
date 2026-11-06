(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: relocated from cgif_file_fuzzer.asan to omx-clap-core fuzz_manifest.asan: 55 address literal(s) rewritten, module paths changed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x94984 7%nat (build_table tfibsegs 0x938d0 9%nat (build_table tfibsegs 0x88a80 3%nat (build_table tfibsegs 0x7fe3c 6%nat (build_table tfibsegs 0x73924 70%nat (build_table tfibsegs 0x732c0 90%nat (build_table tfibsegs 0x6c6d4 8%nat (build_table tfibsegs 0x60a4c 93%nat (build_table tfibsegs 0x5e7f8 18%nat (build_table tfibsegs 0x5c43c 44%nat (build_table tfibsegs 0x5c278 8%nat (build_table tfibsegs 0x5b444 14%nat (build_table tfibsegs 0x5a800 88%nat (build_table tfibsegs 0x59a78 40%nat (build_table tfibsegs 0x58b68 6%nat (build_table tfibsegs 0x54dc4 16%nat (build_table tfibsegs 0x53c48 324%nat (build_table tfibsegs 0x52db8 205%nat (build_table tfibsegs 0x46d18 31%nat (build_table tfibsegs 0x35adc 1016%nat (build_table tfibsegs 0x342f8 96%nat (build_table tfibsegs 0x315ec 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x7301c 145%nat (build_table tfibsegs 0x7293c 169%nat (build_table tfibsegs 0x72654 23%nat (build_table tfibsegs 0x70e4c 45%nat (build_table tfibsegs 0x70340 150%nat (build_table tfibsegs 0x63d78 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6e544 87%nat (build_table tfibsegs 0x6e2b4 100%nat (build_table tfibsegs 0x6c304 75%nat (build_table tfibsegs 0x669a0 131%nat (build_table tfibsegs 0x66300 111%nat (build_table tfibsegs 0x65dd0 128%nat (build_table tfibsegs 0x65cb4 4%nat (build_table tfibsegs 0x65520 2%nat (build_table tfibsegs 0x645d4 27%nat (build_table tfibsegs 0x604d8 26%nat (build_table tfibsegs 0x5fe40 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6da98 8%nat (build_table tfibsegs 0x88128 146%nat (build_table tfibsegs 0x66bac 756%nat (build_table tfibsegs 0x63df4 24%nat (build_table tfibsegs 0x6e544 87%nat (build_table tfibsegs 0x6e2b4 100%nat (build_table tfibsegs 0x6c304 75%nat (build_table tfibsegs 0x669a0 131%nat (build_table tfibsegs 0x66300 111%nat (build_table tfibsegs 0x65dd0 128%nat (build_table tfibsegs 0x65cb4 4%nat (build_table tfibsegs 0x65520 2%nat (build_table tfibsegs 0x645d4 27%nat (build_table tfibsegs 0x604d8 26%nat (build_table tfibsegs 0x5fe40 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
