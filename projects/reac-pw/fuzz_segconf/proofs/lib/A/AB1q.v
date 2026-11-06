(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed and its addresses moved to plugin-hostd/fuzz_command's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AB1q.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x9c9d8 7%nat (build_table tfibsegs 0x9b924 9%nat (build_table tfibsegs 0x908d0 3%nat (build_table tfibsegs 0x84254 6%nat (build_table tfibsegs 0x77d3c 70%nat (build_table tfibsegs 0x776d8 90%nat (build_table tfibsegs 0x70aec 8%nat (build_table tfibsegs 0x64e64 93%nat (build_table tfibsegs 0x62c10 18%nat (build_table tfibsegs 0x60740 44%nat (build_table tfibsegs 0x6057c 8%nat (build_table tfibsegs 0x5f748 14%nat (build_table tfibsegs 0x5eb04 88%nat (build_table tfibsegs 0x5dd7c 40%nat (build_table tfibsegs 0x5ce6c 6%nat (build_table tfibsegs 0x58e78 16%nat (build_table tfibsegs 0x57cfc 324%nat (build_table tfibsegs 0x56c30 206%nat (build_table tfibsegs 0x4a0dc 31%nat (build_table tfibsegs 0x3768c 1016%nat (build_table tfibsegs 0x35ea8 96%nat (build_table tfibsegs 0x330bc 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x77434 145%nat (build_table tfibsegs 0x76d54 169%nat (build_table tfibsegs 0x76a6c 23%nat (build_table tfibsegs 0x75264 45%nat (build_table tfibsegs 0x74758 150%nat (build_table tfibsegs 0x68190 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x7295c 87%nat (build_table tfibsegs 0x726cc 100%nat (build_table tfibsegs 0x7071c 75%nat (build_table tfibsegs 0x6adb8 131%nat (build_table tfibsegs 0x6a718 111%nat (build_table tfibsegs 0x6a1e8 128%nat (build_table tfibsegs 0x6a0cc 4%nat (build_table tfibsegs 0x69938 2%nat (build_table tfibsegs 0x689ec 27%nat (build_table tfibsegs 0x648f0 26%nat (build_table tfibsegs 0x64258 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x71eb0 8%nat (build_table tfibsegs 0x8ff78 146%nat (build_table tfibsegs 0x6afc4 756%nat (build_table tfibsegs 0x6820c 24%nat (build_table tfibsegs 0x7295c 87%nat (build_table tfibsegs 0x726cc 100%nat (build_table tfibsegs 0x7071c 75%nat (build_table tfibsegs 0x6adb8 131%nat (build_table tfibsegs 0x6a718 111%nat (build_table tfibsegs 0x6a1e8 128%nat (build_table tfibsegs 0x6a0cc 4%nat (build_table tfibsegs 0x69938 2%nat (build_table tfibsegs 0x689ec 27%nat (build_table tfibsegs 0x648f0 26%nat (build_table tfibsegs 0x64258 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
