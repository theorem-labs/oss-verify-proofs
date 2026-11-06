(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AB1q.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_rate's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x96bfc 7%nat (build_table tfibsegs 0x95b48 9%nat (build_table tfibsegs 0x8bd10 3%nat (build_table tfibsegs 0x7fc34 6%nat (build_table tfibsegs 0x7371c 70%nat (build_table tfibsegs 0x730b8 90%nat (build_table tfibsegs 0x6c4cc 8%nat (build_table tfibsegs 0x60844 93%nat (build_table tfibsegs 0x5e5f0 18%nat (build_table tfibsegs 0x5c234 44%nat (build_table tfibsegs 0x5c070 8%nat (build_table tfibsegs 0x5b23c 14%nat (build_table tfibsegs 0x5a5f8 88%nat (build_table tfibsegs 0x59870 40%nat (build_table tfibsegs 0x58960 6%nat (build_table tfibsegs 0x54bbc 16%nat (build_table tfibsegs 0x53a40 324%nat (build_table tfibsegs 0x52bb0 205%nat (build_table tfibsegs 0x46b10 31%nat (build_table tfibsegs 0x360ac 1016%nat (build_table tfibsegs 0x348c8 96%nat (build_table tfibsegs 0x31bbc 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x72e14 145%nat (build_table tfibsegs 0x72734 169%nat (build_table tfibsegs 0x7244c 23%nat (build_table tfibsegs 0x70c44 45%nat (build_table tfibsegs 0x70138 150%nat (build_table tfibsegs 0x63b70 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6e33c 87%nat (build_table tfibsegs 0x6e0ac 100%nat (build_table tfibsegs 0x6c0fc 75%nat (build_table tfibsegs 0x66798 131%nat (build_table tfibsegs 0x660f8 111%nat (build_table tfibsegs 0x65bc8 128%nat (build_table tfibsegs 0x65aac 4%nat (build_table tfibsegs 0x65318 2%nat (build_table tfibsegs 0x643cc 27%nat (build_table tfibsegs 0x602d0 26%nat (build_table tfibsegs 0x5fc38 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6d890 8%nat (build_table tfibsegs 0x8b3d4 139%nat (build_table tfibsegs 0x669a4 756%nat (build_table tfibsegs 0x63bec 24%nat (build_table tfibsegs 0x6e33c 87%nat (build_table tfibsegs 0x6e0ac 100%nat (build_table tfibsegs 0x6c0fc 75%nat (build_table tfibsegs 0x66798 131%nat (build_table tfibsegs 0x660f8 111%nat (build_table tfibsegs 0x65bc8 128%nat (build_table tfibsegs 0x65aac 4%nat (build_table tfibsegs 0x65318 2%nat (build_table tfibsegs 0x643cc 27%nat (build_table tfibsegs 0x602d0 26%nat (build_table tfibsegs 0x5fc38 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
