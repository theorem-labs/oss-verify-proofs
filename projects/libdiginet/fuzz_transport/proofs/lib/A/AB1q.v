(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build. *)
(* Relocated from proofs/libreac/fuzz_grant/lib/A/AB1q.v at 25e3d17bdb50 by port_core 83f5203d2a2f onto libdiginet/fuzz_transport (asan). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x9eeb8 7%nat (build_table tfibsegs 0x9de04 9%nat (build_table tfibsegs 0x936ec 3%nat (build_table tfibsegs 0x80784 6%nat (build_table tfibsegs 0x7426c 70%nat (build_table tfibsegs 0x73c08 90%nat (build_table tfibsegs 0x6d01c 8%nat (build_table tfibsegs 0x61394 93%nat (build_table tfibsegs 0x5f140 18%nat (build_table tfibsegs 0x5cd84 44%nat (build_table tfibsegs 0x5cbc0 8%nat (build_table tfibsegs 0x5bd8c 14%nat (build_table tfibsegs 0x5b148 88%nat (build_table tfibsegs 0x5a3c0 40%nat (build_table tfibsegs 0x594b0 6%nat (build_table tfibsegs 0x5570c 16%nat (build_table tfibsegs 0x54590 324%nat (build_table tfibsegs 0x53700 205%nat (build_table tfibsegs 0x47660 31%nat (build_table tfibsegs 0x367a8 1016%nat (build_table tfibsegs 0x34fc4 96%nat (build_table tfibsegs 0x322b8 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x73964 145%nat (build_table tfibsegs 0x73284 169%nat (build_table tfibsegs 0x72f9c 23%nat (build_table tfibsegs 0x71794 45%nat (build_table tfibsegs 0x70c88 150%nat (build_table tfibsegs 0x646c0 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6ee8c 87%nat (build_table tfibsegs 0x6ebfc 100%nat (build_table tfibsegs 0x6cc4c 75%nat (build_table tfibsegs 0x672e8 131%nat (build_table tfibsegs 0x66c48 111%nat (build_table tfibsegs 0x66718 128%nat (build_table tfibsegs 0x665fc 4%nat (build_table tfibsegs 0x65e68 2%nat (build_table tfibsegs 0x64f1c 27%nat (build_table tfibsegs 0x60e20 26%nat (build_table tfibsegs 0x60788 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6e3e0 8%nat (build_table tfibsegs 0x92db0 139%nat (build_table tfibsegs 0x674f4 756%nat (build_table tfibsegs 0x6473c 24%nat (build_table tfibsegs 0x6ee8c 87%nat (build_table tfibsegs 0x6ebfc 100%nat (build_table tfibsegs 0x6cc4c 75%nat (build_table tfibsegs 0x672e8 131%nat (build_table tfibsegs 0x66c48 111%nat (build_table tfibsegs 0x66718 128%nat (build_table tfibsegs 0x665fc 4%nat (build_table tfibsegs 0x65e68 2%nat (build_table tfibsegs 0x64f1c 27%nat (build_table tfibsegs 0x60e20 26%nat (build_table tfibsegs 0x60788 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
