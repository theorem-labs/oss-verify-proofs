(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed and its addresses moved to plugin-hostd/fuzz_command's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AB1q.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AB1q.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x9d184 7%nat (build_table tfibsegs 0x9c0d0 9%nat (build_table tfibsegs 0x9107c 3%nat (build_table tfibsegs 0x842e0 6%nat (build_table tfibsegs 0x77dc8 70%nat (build_table tfibsegs 0x77764 90%nat (build_table tfibsegs 0x70b78 8%nat (build_table tfibsegs 0x64ef0 93%nat (build_table tfibsegs 0x62c9c 18%nat (build_table tfibsegs 0x607cc 44%nat (build_table tfibsegs 0x60608 8%nat (build_table tfibsegs 0x5f7d4 14%nat (build_table tfibsegs 0x5eb90 88%nat (build_table tfibsegs 0x5de08 40%nat (build_table tfibsegs 0x5cef8 6%nat (build_table tfibsegs 0x58f04 16%nat (build_table tfibsegs 0x57d88 324%nat (build_table tfibsegs 0x56cbc 206%nat (build_table tfibsegs 0x4a168 31%nat (build_table tfibsegs 0x37718 1016%nat (build_table tfibsegs 0x35f34 96%nat (build_table tfibsegs 0x33148 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x774c0 145%nat (build_table tfibsegs 0x76de0 169%nat (build_table tfibsegs 0x76af8 23%nat (build_table tfibsegs 0x752f0 45%nat (build_table tfibsegs 0x747e4 150%nat (build_table tfibsegs 0x6821c 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x729e8 87%nat (build_table tfibsegs 0x72758 100%nat (build_table tfibsegs 0x707a8 75%nat (build_table tfibsegs 0x6ae44 131%nat (build_table tfibsegs 0x6a7a4 111%nat (build_table tfibsegs 0x6a274 128%nat (build_table tfibsegs 0x6a158 4%nat (build_table tfibsegs 0x699c4 2%nat (build_table tfibsegs 0x68a78 27%nat (build_table tfibsegs 0x6497c 26%nat (build_table tfibsegs 0x642e4 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x71f3c 8%nat (build_table tfibsegs 0x90724 146%nat (build_table tfibsegs 0x6b050 756%nat (build_table tfibsegs 0x68298 24%nat (build_table tfibsegs 0x729e8 87%nat (build_table tfibsegs 0x72758 100%nat (build_table tfibsegs 0x707a8 75%nat (build_table tfibsegs 0x6ae44 131%nat (build_table tfibsegs 0x6a7a4 111%nat (build_table tfibsegs 0x6a274 128%nat (build_table tfibsegs 0x6a158 4%nat (build_table tfibsegs 0x699c4 2%nat (build_table tfibsegs 0x68a78 27%nat (build_table tfibsegs 0x6497c 26%nat (build_table tfibsegs 0x642e4 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
