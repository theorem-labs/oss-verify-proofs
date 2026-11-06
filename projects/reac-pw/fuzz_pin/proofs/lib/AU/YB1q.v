(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build; AB1v's tfibsegs is A/AWalkFw0.v's. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AB1q.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to reac-pw/fuzz_pin's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AB1q.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_pin's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AB1q.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw0.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x93140 7%nat (build_table tfibsegs 0x9208c 9%nat (build_table tfibsegs 0x877fc 3%nat (build_table tfibsegs 0x7fbd4 6%nat (build_table tfibsegs 0x736bc 70%nat (build_table tfibsegs 0x73058 90%nat (build_table tfibsegs 0x6c46c 8%nat (build_table tfibsegs 0x607e4 93%nat (build_table tfibsegs 0x5e590 18%nat (build_table tfibsegs 0x5c1d4 44%nat (build_table tfibsegs 0x5c010 8%nat (build_table tfibsegs 0x5b1dc 14%nat (build_table tfibsegs 0x5a598 88%nat (build_table tfibsegs 0x59810 40%nat (build_table tfibsegs 0x58900 6%nat (build_table tfibsegs 0x54b5c 16%nat (build_table tfibsegs 0x539e0 324%nat (build_table tfibsegs 0x52b50 205%nat (build_table tfibsegs 0x46cf0 31%nat (build_table tfibsegs 0x359f4 1016%nat (build_table tfibsegs 0x34210 96%nat (build_table tfibsegs 0x31504 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x72db4 145%nat (build_table tfibsegs 0x726d4 169%nat (build_table tfibsegs 0x723ec 23%nat (build_table tfibsegs 0x70be4 45%nat (build_table tfibsegs 0x700d8 150%nat (build_table tfibsegs 0x63b10 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6e2dc 87%nat (build_table tfibsegs 0x6e04c 100%nat (build_table tfibsegs 0x6c09c 75%nat (build_table tfibsegs 0x66738 131%nat (build_table tfibsegs 0x66098 111%nat (build_table tfibsegs 0x65b68 128%nat (build_table tfibsegs 0x65a4c 4%nat (build_table tfibsegs 0x652b8 2%nat (build_table tfibsegs 0x6436c 27%nat (build_table tfibsegs 0x60270 26%nat (build_table tfibsegs 0x5fbd8 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6d830 8%nat (build_table tfibsegs 0x86ec0 139%nat (build_table tfibsegs 0x66944 756%nat (build_table tfibsegs 0x63b8c 24%nat (build_table tfibsegs 0x6e2dc 87%nat (build_table tfibsegs 0x6e04c 100%nat (build_table tfibsegs 0x6c09c 75%nat (build_table tfibsegs 0x66738 131%nat (build_table tfibsegs 0x66098 111%nat (build_table tfibsegs 0x65b68 128%nat (build_table tfibsegs 0x65a4c 4%nat (build_table tfibsegs 0x652b8 2%nat (build_table tfibsegs 0x6436c 27%nat (build_table tfibsegs 0x60270 26%nat (build_table tfibsegs 0x5fbd8 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
