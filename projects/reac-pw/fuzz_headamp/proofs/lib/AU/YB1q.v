(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AB1q.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_role's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_role/lib/A/AB1q.v at 9f8c843f0e03 (image sha256 614cffc0864c), with its module paths changed and its addresses moved to reac-pw/fuzz_headamp's ASan build (image sha256 f3e0669d2819) by alreloc a5c53bb2bed4; comments kept as the source has them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_headamp/lib/A/AB1q.v at b0cad0df5623 (image sha256 f3e0669d2819), with its module names changed (A.Axyz -> AU.Yxyz) and its addresses moved to reac-pw/fuzz_headamp's ASan+UBSan build (image sha256 53edda9bdeeb) by derive_y.py b7b132fb12a7; the Modified-by lines above describe how lib/A/AB1q.v was made and quote its ASan-build values. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x9762c 7%nat (build_table tfibsegs 0x96578 9%nat (build_table tfibsegs 0x8c6e4 3%nat (build_table tfibsegs 0x80160 6%nat (build_table tfibsegs 0x73c48 70%nat (build_table tfibsegs 0x735e4 90%nat (build_table tfibsegs 0x6c9f8 8%nat (build_table tfibsegs 0x60d70 93%nat (build_table tfibsegs 0x5eb1c 18%nat (build_table tfibsegs 0x5c760 44%nat (build_table tfibsegs 0x5c59c 8%nat (build_table tfibsegs 0x5b768 14%nat (build_table tfibsegs 0x5ab24 88%nat (build_table tfibsegs 0x59d9c 40%nat (build_table tfibsegs 0x58e8c 6%nat (build_table tfibsegs 0x550e8 16%nat (build_table tfibsegs 0x53f6c 324%nat (build_table tfibsegs 0x530dc 205%nat (build_table tfibsegs 0x46ab8 31%nat (build_table tfibsegs 0x35e3c 1016%nat (build_table tfibsegs 0x34658 96%nat (build_table tfibsegs 0x3194c 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x73340 145%nat (build_table tfibsegs 0x72c60 169%nat (build_table tfibsegs 0x72978 23%nat (build_table tfibsegs 0x71170 45%nat (build_table tfibsegs 0x70664 150%nat (build_table tfibsegs 0x6409c 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6e868 87%nat (build_table tfibsegs 0x6e5d8 100%nat (build_table tfibsegs 0x6c628 75%nat (build_table tfibsegs 0x66cc4 131%nat (build_table tfibsegs 0x66624 111%nat (build_table tfibsegs 0x660f4 128%nat (build_table tfibsegs 0x65fd8 4%nat (build_table tfibsegs 0x65844 2%nat (build_table tfibsegs 0x648f8 27%nat (build_table tfibsegs 0x607fc 26%nat (build_table tfibsegs 0x60164 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6ddbc 8%nat (build_table tfibsegs 0x8bda8 139%nat (build_table tfibsegs 0x66ed0 756%nat (build_table tfibsegs 0x64118 24%nat (build_table tfibsegs 0x6e868 87%nat (build_table tfibsegs 0x6e5d8 100%nat (build_table tfibsegs 0x6c628 75%nat (build_table tfibsegs 0x66cc4 131%nat (build_table tfibsegs 0x66624 111%nat (build_table tfibsegs 0x660f4 128%nat (build_table tfibsegs 0x65fd8 4%nat (build_table tfibsegs 0x65844 2%nat (build_table tfibsegs 0x648f8 27%nat (build_table tfibsegs 0x607fc 26%nat (build_table tfibsegs 0x60164 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
