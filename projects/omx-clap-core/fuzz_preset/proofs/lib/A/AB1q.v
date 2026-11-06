(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed; its address literals moved to omx-clap-core/fuzz_preset's ASan build where h-mani-a2's maps/reloc-cgif-preset.A.tsv maps them; the literals it does not map are still cgif_file_fuzzer.asan's (listed in the commit that moved them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x9cf5c 7%nat (build_table tfibsegs 0x9bea8 9%nat (build_table tfibsegs 0x8efd8 3%nat (build_table tfibsegs 0x80b00 6%nat (build_table tfibsegs 0x745e8 70%nat (build_table tfibsegs 0x73f84 90%nat (build_table tfibsegs 0x6d398 8%nat (build_table tfibsegs 0x61710 93%nat (build_table tfibsegs 0x5f4bc 18%nat (build_table tfibsegs 0x5d100 44%nat (build_table tfibsegs 0x5cf3c 8%nat (build_table tfibsegs 0x5c108 14%nat (build_table tfibsegs 0x5b4c4 88%nat (build_table tfibsegs 0x5a73c 40%nat (build_table tfibsegs 0x5982c 6%nat (build_table tfibsegs 0x55a88 16%nat (build_table tfibsegs 0x5490c 324%nat (build_table tfibsegs 0x53734 206%nat (build_table tfibsegs 0x47694 31%nat (build_table tfibsegs 0x36c58 1016%nat (build_table tfibsegs 0x35474 96%nat (build_table tfibsegs 0x3255c 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x73ce0 145%nat (build_table tfibsegs 0x73600 169%nat (build_table tfibsegs 0x73318 23%nat (build_table tfibsegs 0x71b10 45%nat (build_table tfibsegs 0x71004 150%nat (build_table tfibsegs 0x64a3c 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6f208 87%nat (build_table tfibsegs 0x6ef78 100%nat (build_table tfibsegs 0x6cfc8 75%nat (build_table tfibsegs 0x67664 131%nat (build_table tfibsegs 0x66fc4 111%nat (build_table tfibsegs 0x66a94 128%nat (build_table tfibsegs 0x66978 4%nat (build_table tfibsegs 0x661e4 2%nat (build_table tfibsegs 0x65298 27%nat (build_table tfibsegs 0x6119c 26%nat (build_table tfibsegs 0x60b04 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6e75c 8%nat (build_table tfibsegs 0x8e69c 139%nat (build_table tfibsegs 0x67870 756%nat (build_table tfibsegs 0x64ab8 24%nat (build_table tfibsegs 0x6f208 87%nat (build_table tfibsegs 0x6ef78 100%nat (build_table tfibsegs 0x6cfc8 75%nat (build_table tfibsegs 0x67664 131%nat (build_table tfibsegs 0x66fc4 111%nat (build_table tfibsegs 0x66a94 128%nat (build_table tfibsegs 0x66978 4%nat (build_table tfibsegs 0x661e4 2%nat (build_table tfibsegs 0x65298 27%nat (build_table tfibsegs 0x6119c 26%nat (build_table tfibsegs 0x60b04 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
