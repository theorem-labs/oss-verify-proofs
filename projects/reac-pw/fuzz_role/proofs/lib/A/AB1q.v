(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AB1q.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_role's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x95654 7%nat (build_table tfibsegs 0x945a0 9%nat (build_table tfibsegs 0x8a76c 3%nat (build_table tfibsegs 0x7f4a8 6%nat (build_table tfibsegs 0x72f90 70%nat (build_table tfibsegs 0x7292c 90%nat (build_table tfibsegs 0x6bd40 8%nat (build_table tfibsegs 0x600b8 93%nat (build_table tfibsegs 0x5de64 18%nat (build_table tfibsegs 0x5baa8 44%nat (build_table tfibsegs 0x5b8e4 8%nat (build_table tfibsegs 0x5aab0 14%nat (build_table tfibsegs 0x59e6c 88%nat (build_table tfibsegs 0x590e4 40%nat (build_table tfibsegs 0x581d4 6%nat (build_table tfibsegs 0x54430 16%nat (build_table tfibsegs 0x532b4 324%nat (build_table tfibsegs 0x52424 205%nat (build_table tfibsegs 0x46384 31%nat (build_table tfibsegs 0x35d0c 1016%nat (build_table tfibsegs 0x34528 96%nat (build_table tfibsegs 0x3181c 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x72688 145%nat (build_table tfibsegs 0x71fa8 169%nat (build_table tfibsegs 0x71cc0 23%nat (build_table tfibsegs 0x704b8 45%nat (build_table tfibsegs 0x6f9ac 150%nat (build_table tfibsegs 0x633e4 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6dbb0 87%nat (build_table tfibsegs 0x6d920 100%nat (build_table tfibsegs 0x6b970 75%nat (build_table tfibsegs 0x6600c 131%nat (build_table tfibsegs 0x6596c 111%nat (build_table tfibsegs 0x6543c 128%nat (build_table tfibsegs 0x65320 4%nat (build_table tfibsegs 0x64b8c 2%nat (build_table tfibsegs 0x63c40 27%nat (build_table tfibsegs 0x5fb44 26%nat (build_table tfibsegs 0x5f4ac 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6d104 8%nat (build_table tfibsegs 0x89e30 139%nat (build_table tfibsegs 0x66218 756%nat (build_table tfibsegs 0x63460 24%nat (build_table tfibsegs 0x6dbb0 87%nat (build_table tfibsegs 0x6d920 100%nat (build_table tfibsegs 0x6b970 75%nat (build_table tfibsegs 0x6600c 131%nat (build_table tfibsegs 0x6596c 111%nat (build_table tfibsegs 0x6543c 128%nat (build_table tfibsegs 0x65320 4%nat (build_table tfibsegs 0x64b8c 2%nat (build_table tfibsegs 0x63c40 27%nat (build_table tfibsegs 0x5fb44 26%nat (build_table tfibsegs 0x5f4ac 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
