(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build; AB1v's tfibsegs is A/AWalkFw0.v's. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AWalkFw0.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x915b0 7%nat (build_table tfibsegs 0x904fc 9%nat (build_table tfibsegs 0x85de8 3%nat (build_table tfibsegs 0x7e3f0 6%nat (build_table tfibsegs 0x71ed8 70%nat (build_table tfibsegs 0x71874 90%nat (build_table tfibsegs 0x6ac88 8%nat (build_table tfibsegs 0x5f000 93%nat (build_table tfibsegs 0x5cdac 18%nat (build_table tfibsegs 0x5a9f0 44%nat (build_table tfibsegs 0x5a82c 8%nat (build_table tfibsegs 0x599f8 14%nat (build_table tfibsegs 0x58db4 88%nat (build_table tfibsegs 0x5802c 40%nat (build_table tfibsegs 0x5711c 6%nat (build_table tfibsegs 0x53378 16%nat (build_table tfibsegs 0x521fc 324%nat (build_table tfibsegs 0x5136c 205%nat (build_table tfibsegs 0x45768 31%nat (build_table tfibsegs 0x35174 1016%nat (build_table tfibsegs 0x33990 96%nat (build_table tfibsegs 0x30c84 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x715d0 145%nat (build_table tfibsegs 0x70ef0 169%nat (build_table tfibsegs 0x70c08 23%nat (build_table tfibsegs 0x6f400 45%nat (build_table tfibsegs 0x6e8f4 150%nat (build_table tfibsegs 0x6232c 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6caf8 87%nat (build_table tfibsegs 0x6c868 100%nat (build_table tfibsegs 0x6a8b8 75%nat (build_table tfibsegs 0x64f54 131%nat (build_table tfibsegs 0x648b4 111%nat (build_table tfibsegs 0x64384 128%nat (build_table tfibsegs 0x64268 4%nat (build_table tfibsegs 0x63ad4 2%nat (build_table tfibsegs 0x62b88 27%nat (build_table tfibsegs 0x5ea8c 26%nat (build_table tfibsegs 0x5e3f4 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6c04c 8%nat (build_table tfibsegs 0x854ac 139%nat (build_table tfibsegs 0x65160 756%nat (build_table tfibsegs 0x623a8 24%nat (build_table tfibsegs 0x6caf8 87%nat (build_table tfibsegs 0x6c868 100%nat (build_table tfibsegs 0x6a8b8 75%nat (build_table tfibsegs 0x64f54 131%nat (build_table tfibsegs 0x648b4 111%nat (build_table tfibsegs 0x64384 128%nat (build_table tfibsegs 0x64268 4%nat (build_table tfibsegs 0x63ad4 2%nat (build_table tfibsegs 0x62b88 27%nat (build_table tfibsegs 0x5ea8c 26%nat (build_table tfibsegs 0x5e3f4 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
