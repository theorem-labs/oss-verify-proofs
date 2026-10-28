(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts AsanMainEntryLemmas.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AH0Spec0 AH0Spec AH0Bridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ARUN_OF.
  Variable sp : word.
  Hypothesis Hsp : valid_sp sp.
  Definition aceil_of : Z := bv_unsigned sp / 4096 * 4096 - 2 ^ 23.
  #[using="Hsp"] Lemma aceil_of_lo : 0x7fff7f800000 <= aceil_of.
  Proof.
    ddestruct Hsp as (LO & HI & AL). unfold sp_window_lo in LO. unfold aceil_of.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). nia.
  Qed.
  #[using="Hsp"] Lemma aceil_of_hi : aceil_of <= 0x7fffff800000.
  Proof.
    ddestruct Hsp as (LO & HI & AL). unfold sp_window_hi in HI. unfold aceil_of.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). nia.
  Qed.
  #[using="Type"] Lemma aceil_of_pg : aceil_of mod 4096 = 0.
  Proof.
    unfold aceil_of. replace (bv_unsigned sp / 4096 * 4096 - 2 ^ 23) with ((bv_unsigned sp / 4096 - 2048) * 4096) by lia. apply Z_mod_mult.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Definition arun_of : arun := {| aceil := aceil_of; aceil_lo := aceil_of_lo; aceil_hi := aceil_of_hi; aceil_pg := aceil_of_pg |}.
  (* [comment removed for export] *)
  #[using="Type"] Lemma HACsp_of : @ACEIL arun_of = bv_unsigned sp / 4096 * 4096 - 2 ^ 23.
  Proof. reflexivity. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma STKLO_OK_of : @ACEIL arun_of <= bv_unsigned sp - 2 ^ 23.
  Proof. change (@ACEIL arun_of) with aceil_of. unfold aceil_of. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). nia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End ARUN_OF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section H0.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Let hAR : arun := arun_of sp Hsp.
  Let STKLO : Z := bv_unsigned sp - 2 ^ 23.

  End H0.
