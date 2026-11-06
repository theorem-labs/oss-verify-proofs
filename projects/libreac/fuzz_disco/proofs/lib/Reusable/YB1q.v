(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Generated for fuzz_disco's asan-ubsan image: each decode window's start is the donor's carried through
   resolve_code.py's function pairing, and its word count is kept because the donor's and the target's instruction
   shapes are equal over the whole window (checked for all windows). table_ok is then re-checked by vm_compute. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP02 YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x9b7b8 7%nat (build_table tfibsegs 0x9a704 9%nat (build_table tfibsegs 0x8ffec 3%nat (build_table tfibsegs 0x804dc 6%nat (build_table tfibsegs 0x73fc4 70%nat (build_table tfibsegs 0x73960 90%nat (build_table tfibsegs 0x6cd74 8%nat (build_table tfibsegs 0x610ec 93%nat (build_table tfibsegs 0x5ee98 18%nat (build_table tfibsegs 0x5cadc 44%nat (build_table tfibsegs 0x5c918 8%nat (build_table tfibsegs 0x5bae4 14%nat (build_table tfibsegs 0x5aea0 88%nat (build_table tfibsegs 0x5a118 40%nat (build_table tfibsegs 0x59208 6%nat (build_table tfibsegs 0x55464 16%nat (build_table tfibsegs 0x542e8 324%nat (build_table tfibsegs 0x53458 205%nat (build_table tfibsegs 0x473b8 31%nat (build_table tfibsegs 0x365fc 1016%nat (build_table tfibsegs 0x34e18 96%nat (build_table tfibsegs 0x3210c 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x736bc 145%nat (build_table tfibsegs 0x72fdc 169%nat (build_table tfibsegs 0x72cf4 23%nat (build_table tfibsegs 0x714ec 45%nat (build_table tfibsegs 0x709e0 150%nat (build_table tfibsegs 0x64418 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6ebe4 87%nat (build_table tfibsegs 0x6e954 100%nat (build_table tfibsegs 0x6c9a4 75%nat (build_table tfibsegs 0x67040 131%nat (build_table tfibsegs 0x669a0 111%nat (build_table tfibsegs 0x66470 128%nat (build_table tfibsegs 0x66354 4%nat (build_table tfibsegs 0x65bc0 2%nat (build_table tfibsegs 0x64c74 27%nat (build_table tfibsegs 0x60b78 26%nat (build_table tfibsegs 0x604e0 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6e138 8%nat (build_table tfibsegs 0x8f6b0 139%nat (build_table tfibsegs 0x6724c 756%nat (build_table tfibsegs 0x64494 24%nat (build_table tfibsegs 0x6ebe4 87%nat (build_table tfibsegs 0x6e954 100%nat (build_table tfibsegs 0x6c9a4 75%nat (build_table tfibsegs 0x67040 131%nat (build_table tfibsegs 0x669a0 111%nat (build_table tfibsegs 0x66470 128%nat (build_table tfibsegs 0x66354 4%nat (build_table tfibsegs 0x65bc0 2%nat (build_table tfibsegs 0x64c74 27%nat (build_table tfibsegs 0x60b78 26%nat (build_table tfibsegs 0x604e0 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
