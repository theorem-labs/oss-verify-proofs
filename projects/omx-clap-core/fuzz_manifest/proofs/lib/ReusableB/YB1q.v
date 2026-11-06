(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1q.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to omx-clap-core/fuzz_manifest's ASan build. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x94c6c 7%nat (build_table tfibsegs 0x93bb8 9%nat (build_table tfibsegs 0x88d68 3%nat (build_table tfibsegs 0x7fe9c 6%nat (build_table tfibsegs 0x73984 70%nat (build_table tfibsegs 0x73320 90%nat (build_table tfibsegs 0x6c734 8%nat (build_table tfibsegs 0x60aac 93%nat (build_table tfibsegs 0x5e858 18%nat (build_table tfibsegs 0x5c49c 44%nat (build_table tfibsegs 0x5c2d8 8%nat (build_table tfibsegs 0x5b4a4 14%nat (build_table tfibsegs 0x5a860 88%nat (build_table tfibsegs 0x59ad8 40%nat (build_table tfibsegs 0x58bc8 6%nat (build_table tfibsegs 0x54e24 16%nat (build_table tfibsegs 0x53ca8 324%nat (build_table tfibsegs 0x52e18 205%nat (build_table tfibsegs 0x46d78 31%nat (build_table tfibsegs 0x35b3c 1016%nat (build_table tfibsegs 0x34358 96%nat (build_table tfibsegs 0x3164c 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x7307c 145%nat (build_table tfibsegs 0x7299c 169%nat (build_table tfibsegs 0x726b4 23%nat (build_table tfibsegs 0x70eac 45%nat (build_table tfibsegs 0x703a0 150%nat (build_table tfibsegs 0x63dd8 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6e5a4 87%nat (build_table tfibsegs 0x6e314 100%nat (build_table tfibsegs 0x6c364 75%nat (build_table tfibsegs 0x66a00 131%nat (build_table tfibsegs 0x66360 111%nat (build_table tfibsegs 0x65e30 128%nat (build_table tfibsegs 0x65d14 4%nat (build_table tfibsegs 0x65580 2%nat (build_table tfibsegs 0x64634 27%nat (build_table tfibsegs 0x60538 26%nat (build_table tfibsegs 0x5fea0 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6daf8 8%nat (build_table tfibsegs 0x88410 146%nat (build_table tfibsegs 0x66c0c 756%nat (build_table tfibsegs 0x63e54 24%nat (build_table tfibsegs 0x6e5a4 87%nat (build_table tfibsegs 0x6e314 100%nat (build_table tfibsegs 0x6c364 75%nat (build_table tfibsegs 0x66a00 131%nat (build_table tfibsegs 0x66360 111%nat (build_table tfibsegs 0x65e30 128%nat (build_table tfibsegs 0x65d14 4%nat (build_table tfibsegs 0x65580 2%nat (build_table tfibsegs 0x64634 27%nat (build_table tfibsegs 0x60538 26%nat (build_table tfibsegs 0x5fea0 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
