(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AB1q.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_role's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AB1q.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_role's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AB1q.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x958f4 7%nat (build_table tfibsegs 0x94840 9%nat (build_table tfibsegs 0x8aa0c 3%nat (build_table tfibsegs 0x7f540 6%nat (build_table tfibsegs 0x73028 70%nat (build_table tfibsegs 0x729c4 90%nat (build_table tfibsegs 0x6bdd8 8%nat (build_table tfibsegs 0x60150 93%nat (build_table tfibsegs 0x5defc 18%nat (build_table tfibsegs 0x5bb40 44%nat (build_table tfibsegs 0x5b97c 8%nat (build_table tfibsegs 0x5ab48 14%nat (build_table tfibsegs 0x59f04 88%nat (build_table tfibsegs 0x5917c 40%nat (build_table tfibsegs 0x5826c 6%nat (build_table tfibsegs 0x544c8 16%nat (build_table tfibsegs 0x5334c 324%nat (build_table tfibsegs 0x524bc 205%nat (build_table tfibsegs 0x4641c 31%nat (build_table tfibsegs 0x35d84 1016%nat (build_table tfibsegs 0x345a0 96%nat (build_table tfibsegs 0x31894 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x72720 145%nat (build_table tfibsegs 0x72040 169%nat (build_table tfibsegs 0x71d58 23%nat (build_table tfibsegs 0x70550 45%nat (build_table tfibsegs 0x6fa44 150%nat (build_table tfibsegs 0x6347c 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6dc48 87%nat (build_table tfibsegs 0x6d9b8 100%nat (build_table tfibsegs 0x6ba08 75%nat (build_table tfibsegs 0x660a4 131%nat (build_table tfibsegs 0x65a04 111%nat (build_table tfibsegs 0x654d4 128%nat (build_table tfibsegs 0x653b8 4%nat (build_table tfibsegs 0x64c24 2%nat (build_table tfibsegs 0x63cd8 27%nat (build_table tfibsegs 0x5fbdc 26%nat (build_table tfibsegs 0x5f544 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6d19c 8%nat (build_table tfibsegs 0x8a0d0 139%nat (build_table tfibsegs 0x662b0 756%nat (build_table tfibsegs 0x634f8 24%nat (build_table tfibsegs 0x6dc48 87%nat (build_table tfibsegs 0x6d9b8 100%nat (build_table tfibsegs 0x6ba08 75%nat (build_table tfibsegs 0x660a4 131%nat (build_table tfibsegs 0x65a04 111%nat (build_table tfibsegs 0x654d4 128%nat (build_table tfibsegs 0x653b8 4%nat (build_table tfibsegs 0x64c24 2%nat (build_table tfibsegs 0x63cd8 27%nat (build_table tfibsegs 0x5fbdc 26%nat (build_table tfibsegs 0x5f544 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
