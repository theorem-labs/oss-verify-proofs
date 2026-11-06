(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/AB1q.v (donor image sha256 c2c7559b29bd), with its module paths changed and its addresses moved to libreac/fuzz_decode's ASan build; the tfibtbl_rtA range at 0x51f60 (__interceptor_trampoline_free through ___interceptor_malloc) is 206 words, not the donor's 205, because fuzz_decode.asan has one more trampoline in it (__interceptor_trampoline_calloc at 0x51f68), so ___interceptor_malloc's ret (0x52294) is word 206. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x93d18 7%nat (build_table tfibsegs 0x92c64 9%nat (build_table tfibsegs 0x8854c 3%nat (build_table tfibsegs 0x7f584 6%nat (build_table tfibsegs 0x7306c 70%nat (build_table tfibsegs 0x72a08 90%nat (build_table tfibsegs 0x6be1c 8%nat (build_table tfibsegs 0x60194 93%nat (build_table tfibsegs 0x5df40 18%nat (build_table tfibsegs 0x5ba70 44%nat (build_table tfibsegs 0x5b8ac 8%nat (build_table tfibsegs 0x5aa78 14%nat (build_table tfibsegs 0x59e34 88%nat (build_table tfibsegs 0x590ac 40%nat (build_table tfibsegs 0x5819c 6%nat (build_table tfibsegs 0x541a8 16%nat (build_table tfibsegs 0x5302c 324%nat (build_table tfibsegs 0x51f60 206%nat (build_table tfibsegs 0x45ec0 31%nat (build_table tfibsegs 0x357c0 1016%nat (build_table tfibsegs 0x33fdc 96%nat (build_table tfibsegs 0x311f0 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x72764 145%nat (build_table tfibsegs 0x72084 169%nat (build_table tfibsegs 0x71d9c 23%nat (build_table tfibsegs 0x70594 45%nat (build_table tfibsegs 0x6fa88 150%nat (build_table tfibsegs 0x634c0 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6dc8c 87%nat (build_table tfibsegs 0x6d9fc 100%nat (build_table tfibsegs 0x6ba4c 75%nat (build_table tfibsegs 0x660e8 131%nat (build_table tfibsegs 0x65a48 111%nat (build_table tfibsegs 0x65518 128%nat (build_table tfibsegs 0x653fc 4%nat (build_table tfibsegs 0x64c68 2%nat (build_table tfibsegs 0x63d1c 27%nat (build_table tfibsegs 0x5fc20 26%nat (build_table tfibsegs 0x5f588 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6d1e0 8%nat (build_table tfibsegs 0x87c10 139%nat (build_table tfibsegs 0x662f4 756%nat (build_table tfibsegs 0x6353c 24%nat (build_table tfibsegs 0x6dc8c 87%nat (build_table tfibsegs 0x6d9fc 100%nat (build_table tfibsegs 0x6ba4c 75%nat (build_table tfibsegs 0x660e8 131%nat (build_table tfibsegs 0x65a48 111%nat (build_table tfibsegs 0x65518 128%nat (build_table tfibsegs 0x653fc 4%nat (build_table tfibsegs 0x64c68 2%nat (build_table tfibsegs 0x63d1c 27%nat (build_table tfibsegs 0x5fc20 26%nat (build_table tfibsegs 0x5f588 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
