(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AB1q.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_role's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_role/lib/A/AB1q.v at 9f8c843f0e03 (image sha256 614cffc0864c), with its module paths changed and its addresses moved to reac-pw/fuzz_headamp's ASan build (image sha256 f3e0669d2819) by alreloc a5c53bb2bed4; comments kept as the source has them. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x971b4 7%nat (build_table tfibsegs 0x96100 9%nat (build_table tfibsegs 0x8c26c 3%nat (build_table tfibsegs 0x800e0 6%nat (build_table tfibsegs 0x73bc8 70%nat (build_table tfibsegs 0x73564 90%nat (build_table tfibsegs 0x6c978 8%nat (build_table tfibsegs 0x60cf0 93%nat (build_table tfibsegs 0x5ea9c 18%nat (build_table tfibsegs 0x5c6e0 44%nat (build_table tfibsegs 0x5c51c 8%nat (build_table tfibsegs 0x5b6e8 14%nat (build_table tfibsegs 0x5aaa4 88%nat (build_table tfibsegs 0x59d1c 40%nat (build_table tfibsegs 0x58e0c 6%nat (build_table tfibsegs 0x55068 16%nat (build_table tfibsegs 0x53eec 324%nat (build_table tfibsegs 0x5305c 205%nat (build_table tfibsegs 0x46a38 31%nat (build_table tfibsegs 0x35dbc 1016%nat (build_table tfibsegs 0x345d8 96%nat (build_table tfibsegs 0x318cc 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x732c0 145%nat (build_table tfibsegs 0x72be0 169%nat (build_table tfibsegs 0x728f8 23%nat (build_table tfibsegs 0x710f0 45%nat (build_table tfibsegs 0x705e4 150%nat (build_table tfibsegs 0x6401c 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6e7e8 87%nat (build_table tfibsegs 0x6e558 100%nat (build_table tfibsegs 0x6c5a8 75%nat (build_table tfibsegs 0x66c44 131%nat (build_table tfibsegs 0x665a4 111%nat (build_table tfibsegs 0x66074 128%nat (build_table tfibsegs 0x65f58 4%nat (build_table tfibsegs 0x657c4 2%nat (build_table tfibsegs 0x64878 27%nat (build_table tfibsegs 0x6077c 26%nat (build_table tfibsegs 0x600e4 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6dd3c 8%nat (build_table tfibsegs 0x8b930 139%nat (build_table tfibsegs 0x66e50 756%nat (build_table tfibsegs 0x64098 24%nat (build_table tfibsegs 0x6e7e8 87%nat (build_table tfibsegs 0x6e558 100%nat (build_table tfibsegs 0x6c5a8 75%nat (build_table tfibsegs 0x66c44 131%nat (build_table tfibsegs 0x665a4 111%nat (build_table tfibsegs 0x66074 128%nat (build_table tfibsegs 0x65f58 4%nat (build_table tfibsegs 0x657c4 2%nat (build_table tfibsegs 0x64878 27%nat (build_table tfibsegs 0x6077c 26%nat (build_table tfibsegs 0x600e4 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
