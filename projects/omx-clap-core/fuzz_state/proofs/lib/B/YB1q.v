(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1q.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan+UBSan build (fuzz_state.asan-ubsan). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x9abe4 7%nat (build_table tfibsegs 0x99b30 9%nat (build_table tfibsegs 0x8cc60 3%nat (build_table tfibsegs 0x804ac 6%nat (build_table tfibsegs 0x73f94 70%nat (build_table tfibsegs 0x73930 90%nat (build_table tfibsegs 0x6cd44 8%nat (build_table tfibsegs 0x610bc 93%nat (build_table tfibsegs 0x5ee68 18%nat (build_table tfibsegs 0x5caac 44%nat (build_table tfibsegs 0x5c8e8 8%nat (build_table tfibsegs 0x5bab4 14%nat (build_table tfibsegs 0x5ae70 88%nat (build_table tfibsegs 0x5a0e8 40%nat (build_table tfibsegs 0x591d8 6%nat (build_table tfibsegs 0x55434 16%nat (build_table tfibsegs 0x542b8 324%nat (build_table tfibsegs 0x530e0 206%nat (build_table tfibsegs 0x47040 31%nat (build_table tfibsegs 0x36604 1016%nat (build_table tfibsegs 0x34e20 96%nat (build_table tfibsegs 0x31f08 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x7368c 145%nat (build_table tfibsegs 0x72fac 169%nat (build_table tfibsegs 0x72cc4 23%nat (build_table tfibsegs 0x714bc 45%nat (build_table tfibsegs 0x709b0 150%nat (build_table tfibsegs 0x643e8 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6ebb4 87%nat (build_table tfibsegs 0x6e924 100%nat (build_table tfibsegs 0x6c974 75%nat (build_table tfibsegs 0x67010 131%nat (build_table tfibsegs 0x66970 111%nat (build_table tfibsegs 0x66440 128%nat (build_table tfibsegs 0x66324 4%nat (build_table tfibsegs 0x65b90 2%nat (build_table tfibsegs 0x64c44 27%nat (build_table tfibsegs 0x60b48 26%nat (build_table tfibsegs 0x604b0 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6e108 8%nat (build_table tfibsegs 0x8c324 139%nat (build_table tfibsegs 0x6721c 756%nat (build_table tfibsegs 0x64464 24%nat (build_table tfibsegs 0x6ebb4 87%nat (build_table tfibsegs 0x6e924 100%nat (build_table tfibsegs 0x6c974 75%nat (build_table tfibsegs 0x67010 131%nat (build_table tfibsegs 0x66970 111%nat (build_table tfibsegs 0x66440 128%nat (build_table tfibsegs 0x66324 4%nat (build_table tfibsegs 0x65b90 2%nat (build_table tfibsegs 0x64c44 27%nat (build_table tfibsegs 0x60b48 26%nat (build_table tfibsegs 0x604b0 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
