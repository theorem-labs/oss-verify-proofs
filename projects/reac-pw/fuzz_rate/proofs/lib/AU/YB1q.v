(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AB1q.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_rate's ASan build. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/AB1q.v at 4e3a0a9ad299, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/AB1q.v was made and quote that file's image-A values; the code below carries image B's values. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x96f04 7%nat (build_table tfibsegs 0x95e50 9%nat (build_table tfibsegs 0x8c018 3%nat (build_table tfibsegs 0x7fc8c 6%nat (build_table tfibsegs 0x73774 70%nat (build_table tfibsegs 0x73110 90%nat (build_table tfibsegs 0x6c524 8%nat (build_table tfibsegs 0x6089c 93%nat (build_table tfibsegs 0x5e648 18%nat (build_table tfibsegs 0x5c28c 44%nat (build_table tfibsegs 0x5c0c8 8%nat (build_table tfibsegs 0x5b294 14%nat (build_table tfibsegs 0x5a650 88%nat (build_table tfibsegs 0x598c8 40%nat (build_table tfibsegs 0x589b8 6%nat (build_table tfibsegs 0x54c14 16%nat (build_table tfibsegs 0x53a98 324%nat (build_table tfibsegs 0x52c08 205%nat (build_table tfibsegs 0x46b68 31%nat (build_table tfibsegs 0x360e4 1016%nat (build_table tfibsegs 0x34900 96%nat (build_table tfibsegs 0x31bf4 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x72e6c 145%nat (build_table tfibsegs 0x7278c 169%nat (build_table tfibsegs 0x724a4 23%nat (build_table tfibsegs 0x70c9c 45%nat (build_table tfibsegs 0x70190 150%nat (build_table tfibsegs 0x63bc8 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6e394 87%nat (build_table tfibsegs 0x6e104 100%nat (build_table tfibsegs 0x6c154 75%nat (build_table tfibsegs 0x667f0 131%nat (build_table tfibsegs 0x66150 111%nat (build_table tfibsegs 0x65c20 128%nat (build_table tfibsegs 0x65b04 4%nat (build_table tfibsegs 0x65370 2%nat (build_table tfibsegs 0x64424 27%nat (build_table tfibsegs 0x60328 26%nat (build_table tfibsegs 0x5fc90 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6d8e8 8%nat (build_table tfibsegs 0x8b6dc 139%nat (build_table tfibsegs 0x669fc 756%nat (build_table tfibsegs 0x63c44 24%nat (build_table tfibsegs 0x6e394 87%nat (build_table tfibsegs 0x6e104 100%nat (build_table tfibsegs 0x6c154 75%nat (build_table tfibsegs 0x667f0 131%nat (build_table tfibsegs 0x66150 111%nat (build_table tfibsegs 0x65c20 128%nat (build_table tfibsegs 0x65b04 4%nat (build_table tfibsegs 0x65370 2%nat (build_table tfibsegs 0x64424 27%nat (build_table tfibsegs 0x60328 26%nat (build_table tfibsegs 0x5fc90 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
