(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AB1q.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build; AB1v's tfibsegs is A/AWalkFw0.v's. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_knock/proofs/lib/A/AB1q.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to libdiginet/fuzz_codec's ASan build. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x987a0 7%nat (build_table tfibsegs 0x976ec 9%nat (build_table tfibsegs 0x8cfd4 3%nat (build_table tfibsegs 0x7fd6c 6%nat (build_table tfibsegs 0x73854 70%nat (build_table tfibsegs 0x731f0 90%nat (build_table tfibsegs 0x6c604 8%nat (build_table tfibsegs 0x6097c 93%nat (build_table tfibsegs 0x5e728 18%nat (build_table tfibsegs 0x5c36c 44%nat (build_table tfibsegs 0x5c1a8 8%nat (build_table tfibsegs 0x5b374 14%nat (build_table tfibsegs 0x5a730 88%nat (build_table tfibsegs 0x599a8 40%nat (build_table tfibsegs 0x58a98 6%nat (build_table tfibsegs 0x54cf4 16%nat (build_table tfibsegs 0x53b78 324%nat (build_table tfibsegs 0x52ce8 205%nat (build_table tfibsegs 0x46c48 31%nat (build_table tfibsegs 0x3620c 1016%nat (build_table tfibsegs 0x34a28 96%nat (build_table tfibsegs 0x31d1c 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x72f4c 145%nat (build_table tfibsegs 0x7286c 169%nat (build_table tfibsegs 0x72584 23%nat (build_table tfibsegs 0x70d7c 45%nat (build_table tfibsegs 0x70270 150%nat (build_table tfibsegs 0x63ca8 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6e474 87%nat (build_table tfibsegs 0x6e1e4 100%nat (build_table tfibsegs 0x6c234 75%nat (build_table tfibsegs 0x668d0 131%nat (build_table tfibsegs 0x66230 111%nat (build_table tfibsegs 0x65d00 128%nat (build_table tfibsegs 0x65be4 4%nat (build_table tfibsegs 0x65450 2%nat (build_table tfibsegs 0x64504 27%nat (build_table tfibsegs 0x60408 26%nat (build_table tfibsegs 0x5fd70 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6d9c8 8%nat (build_table tfibsegs 0x8c698 139%nat (build_table tfibsegs 0x66adc 756%nat (build_table tfibsegs 0x63d24 24%nat (build_table tfibsegs 0x6e474 87%nat (build_table tfibsegs 0x6e1e4 100%nat (build_table tfibsegs 0x6c234 75%nat (build_table tfibsegs 0x668d0 131%nat (build_table tfibsegs 0x66230 111%nat (build_table tfibsegs 0x65d00 128%nat (build_table tfibsegs 0x65be4 4%nat (build_table tfibsegs 0x65450 2%nat (build_table tfibsegs 0x64504 27%nat (build_table tfibsegs 0x60408 26%nat (build_table tfibsegs 0x5fd70 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
