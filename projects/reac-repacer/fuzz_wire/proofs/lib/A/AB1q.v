(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v at 25e3d17bdb50, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/AB1q.v at 4f87de75d67 (donor image sha256 c2c7559b29bd), with its module paths changed and its addresses moved to reac-repacer/fuzz_wire's ASan build. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x937bc 7%nat (build_table tfibsegs 0x92708 9%nat (build_table tfibsegs 0x87ff0 3%nat (build_table tfibsegs 0x7f378 6%nat (build_table tfibsegs 0x72e60 70%nat (build_table tfibsegs 0x727fc 90%nat (build_table tfibsegs 0x6bc10 8%nat (build_table tfibsegs 0x5ff88 93%nat (build_table tfibsegs 0x5dd34 18%nat (build_table tfibsegs 0x5b978 44%nat (build_table tfibsegs 0x5b7b4 8%nat (build_table tfibsegs 0x5a980 14%nat (build_table tfibsegs 0x59d3c 88%nat (build_table tfibsegs 0x58fb4 40%nat (build_table tfibsegs 0x580a4 6%nat (build_table tfibsegs 0x54300 16%nat (build_table tfibsegs 0x53184 324%nat (build_table tfibsegs 0x522f4 205%nat (build_table tfibsegs 0x45ee4 31%nat (build_table tfibsegs 0x35654 1016%nat (build_table tfibsegs 0x33e70 96%nat (build_table tfibsegs 0x31164 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x72558 145%nat (build_table tfibsegs 0x71e78 169%nat (build_table tfibsegs 0x71b90 23%nat (build_table tfibsegs 0x70388 45%nat (build_table tfibsegs 0x6f87c 150%nat (build_table tfibsegs 0x632b4 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6da80 87%nat (build_table tfibsegs 0x6d7f0 100%nat (build_table tfibsegs 0x6b840 75%nat (build_table tfibsegs 0x65edc 131%nat (build_table tfibsegs 0x6583c 111%nat (build_table tfibsegs 0x6530c 128%nat (build_table tfibsegs 0x651f0 4%nat (build_table tfibsegs 0x64a5c 2%nat (build_table tfibsegs 0x63b10 27%nat (build_table tfibsegs 0x5fa14 26%nat (build_table tfibsegs 0x5f37c 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6cfd4 8%nat (build_table tfibsegs 0x876b4 139%nat (build_table tfibsegs 0x660e8 756%nat (build_table tfibsegs 0x63330 24%nat (build_table tfibsegs 0x6da80 87%nat (build_table tfibsegs 0x6d7f0 100%nat (build_table tfibsegs 0x6b840 75%nat (build_table tfibsegs 0x65edc 131%nat (build_table tfibsegs 0x6583c 111%nat (build_table tfibsegs 0x6530c 128%nat (build_table tfibsegs 0x651f0 4%nat (build_table tfibsegs 0x64a5c 2%nat (build_table tfibsegs 0x63b10 27%nat (build_table tfibsegs 0x5fa14 26%nat (build_table tfibsegs 0x5f37c 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
