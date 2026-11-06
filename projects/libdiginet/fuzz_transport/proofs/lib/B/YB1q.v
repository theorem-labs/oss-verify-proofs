(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1q.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_decode's ASan build. *)
(* Relocated from proofs/libreac/fuzz_decode/lib/YB1q.v at 88154566652a by port_core 83f5203d2a2f onto libdiginet/fuzz_transport (asan-ubsan). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YP02. From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x9eb14 7%nat (build_table tfibsegs 0x9da60 9%nat (build_table tfibsegs 0x93348 3%nat (build_table tfibsegs 0x807c0 6%nat (build_table tfibsegs 0x742a8 70%nat (build_table tfibsegs 0x73c44 90%nat (build_table tfibsegs 0x6d058 8%nat (build_table tfibsegs 0x613d0 93%nat (build_table tfibsegs 0x5f17c 18%nat (build_table tfibsegs 0x5cdc0 44%nat (build_table tfibsegs 0x5cbfc 8%nat (build_table tfibsegs 0x5bdc8 14%nat (build_table tfibsegs 0x5b184 88%nat (build_table tfibsegs 0x5a3fc 40%nat (build_table tfibsegs 0x594ec 6%nat (build_table tfibsegs 0x55748 16%nat (build_table tfibsegs 0x545cc 324%nat (build_table tfibsegs 0x5373c 205%nat (build_table tfibsegs 0x4769c 31%nat (build_table tfibsegs 0x36804 1016%nat (build_table tfibsegs 0x35020 96%nat (build_table tfibsegs 0x32314 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x739a0 145%nat (build_table tfibsegs 0x732c0 169%nat (build_table tfibsegs 0x72fd8 23%nat (build_table tfibsegs 0x717d0 45%nat (build_table tfibsegs 0x70cc4 150%nat (build_table tfibsegs 0x646fc 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6eec8 87%nat (build_table tfibsegs 0x6ec38 100%nat (build_table tfibsegs 0x6cc88 75%nat (build_table tfibsegs 0x67324 131%nat (build_table tfibsegs 0x66c84 111%nat (build_table tfibsegs 0x66754 128%nat (build_table tfibsegs 0x66638 4%nat (build_table tfibsegs 0x65ea4 2%nat (build_table tfibsegs 0x64f58 27%nat (build_table tfibsegs 0x60e5c 26%nat (build_table tfibsegs 0x607c4 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6e41c 8%nat (build_table tfibsegs 0x92a0c 139%nat (build_table tfibsegs 0x67530 756%nat (build_table tfibsegs 0x64778 24%nat (build_table tfibsegs 0x6eec8 87%nat (build_table tfibsegs 0x6ec38 100%nat (build_table tfibsegs 0x6cc88 75%nat (build_table tfibsegs 0x67324 131%nat (build_table tfibsegs 0x66c84 111%nat (build_table tfibsegs 0x66754 128%nat (build_table tfibsegs 0x66638 4%nat (build_table tfibsegs 0x65ea4 2%nat (build_table tfibsegs 0x64f58 27%nat (build_table tfibsegs 0x60e5c 26%nat (build_table tfibsegs 0x607c4 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
