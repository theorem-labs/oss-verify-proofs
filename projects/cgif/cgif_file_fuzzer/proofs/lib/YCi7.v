(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YI04 YI09 YI08.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac k17 HK K := assert (C17 : K = 0 \/ K = 1 \/ K = 2 \/ K = 3 \/ K = 4 \/ K = 5 \/ K = 6 \/ K = 7 \/ K = 8 \/ K = 9 \/ K = 10 \/ K = 11 \/
K = 12 \/ K = 13 \/ K = 14 \/ K = 15 \/ K = 16) by (clear - HK; lia);
destruct C17 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]].
Lemma U_tK : forall E k K, ew E k = Z_to_bv 64 K -> 0 <= K <= 16 -> U E (SAlu ALU_AND (SOff k 0) (SLit 255)) = K.
Proof. intros E k K HE HK. unfold U. cbn [sv_denot]. rewrite HE. k17 HK K; vm_compute; reflexivity. Qed.
Lemma U_t0 : forall E k K, ew E k = Z_to_bv 64 K -> 0 <= K <= 16 ->
U E (SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SAlu ALU_AND (SOff k 0) (SLit 255))) (SLit (-1))) = 2 ^ K - 1.
Proof. intros E k K HE HK. unfold U. cbn [sv_denot]. rewrite HE. k17 HK K; vm_compute; reflexivity. Qed.
Lemma U_t0b : forall E k K, ew E k = Z_to_bv 64 K -> 0 <= K <= 16 ->
U E (SAlu ALU_AND (SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SAlu ALU_AND (SOff k 0) (SLit 255))) (SLit (-1))) (SLit 255)) = (2 ^ K - 1) mod 256.
Proof. intros E k K HE HK. unfold U. cbn [sv_denot]. rewrite HE. k17 HK K; vm_compute; reflexivity. Qed.
Lemma U_t1 : forall E k K, ew E k = Z_to_bv 64 K -> 0 <= K <= 16 ->
U E (SAlu ALU_ADD (SAluw ALU_SLL (SLit 2) (SAlu ALU_AND (SOff k 0) (SLit 255))) (SLit (-1))) = 2 ^ (K + 1) - 1.
Proof. intros E k K HE HK. unfold U. cbn [sv_denot]. rewrite HE. k17 HK K; vm_compute; reflexivity. Qed.
Lemma U_t0B : forall E k K, ew E k = Z_to_bv 64 K -> 0 <= K <= 16 ->
U E (SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SOff k 0)) (SLit (-1))) = 2 ^ K - 1.
Proof. intros E k K HE HK. unfold U. cbn [sv_denot]. rewrite HE. k17 HK K; vm_compute; reflexivity. Qed.
Lemma U_t0bB : forall E k K, ew E k = Z_to_bv 64 K -> 0 <= K <= 16 ->
U E (SAlu ALU_AND (SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SOff k 0)) (SLit (-1))) (SLit 255)) = (2 ^ K - 1) mod 256.
Proof. intros E k K HE HK. unfold U. cbn [sv_denot]. rewrite HE. k17 HK K; vm_compute; reflexivity. Qed.
Lemma U_t1B : forall E k K, ew E k = Z_to_bv 64 K -> 0 <= K <= 16 ->
U E (SAlu ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff k 0)) (SLit (-1))) = 2 ^ (K + 1) - 1.
Proof. intros E k K HE HK. unfold U. cbn [sv_denot]. rewrite HE. k17 HK K; vm_compute; reflexivity. Qed.
