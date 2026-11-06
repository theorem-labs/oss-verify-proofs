(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x976d4 7%nat (build_table tfibsegs 0x96620 9%nat (build_table tfibsegs 0x8bf08 3%nat (build_table tfibsegs 0x7fbd0 6%nat (build_table tfibsegs 0x736b8 70%nat (build_table tfibsegs 0x73054 90%nat (build_table tfibsegs 0x6c468 8%nat (build_table tfibsegs 0x607e0 93%nat (build_table tfibsegs 0x5e58c 18%nat (build_table tfibsegs 0x5c1d0 44%nat (build_table tfibsegs 0x5c00c 8%nat (build_table tfibsegs 0x5b1d8 14%nat (build_table tfibsegs 0x5a594 88%nat (build_table tfibsegs 0x5980c 40%nat (build_table tfibsegs 0x588fc 6%nat (build_table tfibsegs 0x54b58 16%nat (build_table tfibsegs 0x539dc 324%nat (build_table tfibsegs 0x52b4c 205%nat (build_table tfibsegs 0x46aac 31%nat (build_table tfibsegs 0x35eb4 1016%nat (build_table tfibsegs 0x346d0 96%nat (build_table tfibsegs 0x319c4 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x72db0 145%nat (build_table tfibsegs 0x726d0 169%nat (build_table tfibsegs 0x723e8 23%nat (build_table tfibsegs 0x70be0 45%nat (build_table tfibsegs 0x700d4 150%nat (build_table tfibsegs 0x63b0c 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6e2d8 87%nat (build_table tfibsegs 0x6e048 100%nat (build_table tfibsegs 0x6c098 75%nat (build_table tfibsegs 0x66734 131%nat (build_table tfibsegs 0x66094 111%nat (build_table tfibsegs 0x65b64 128%nat (build_table tfibsegs 0x65a48 4%nat (build_table tfibsegs 0x652b4 2%nat (build_table tfibsegs 0x64368 27%nat (build_table tfibsegs 0x6026c 26%nat (build_table tfibsegs 0x5fbd4 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6d82c 8%nat (build_table tfibsegs 0x8b5cc 139%nat (build_table tfibsegs 0x66940 756%nat (build_table tfibsegs 0x63b88 24%nat (build_table tfibsegs 0x6e2d8 87%nat (build_table tfibsegs 0x6e048 100%nat (build_table tfibsegs 0x6c098 75%nat (build_table tfibsegs 0x66734 131%nat (build_table tfibsegs 0x66094 111%nat (build_table tfibsegs 0x65b64 128%nat (build_table tfibsegs 0x65a48 4%nat (build_table tfibsegs 0x652b4 2%nat (build_table tfibsegs 0x64368 27%nat (build_table tfibsegs 0x6026c 26%nat (build_table tfibsegs 0x5fbd4 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
