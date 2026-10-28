(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
(* [comment removed for export] *)
Record kinv {hAR : arun} (L : asan_layout) (CS : Z -> Prop) (K : Model -> Prop) := {
  ki_halted : forall mo, K mo -> m_halted mo = None;
  (* [comment removed for export] *)
  ki_top : forall mo, K mo -> atop_ok (alloc_top (m_vmmaps mo));
  ki_mat : forall mo acc, K mo -> acc_ok L CS acc ->
      exists mo', materialize_model_accesses mo acc = Some mo' /\ K mo' /\ mo_mat mo mo' }.

Arguments kinv {hAR} L CS K.
Arguments ki_halted {hAR L CS K}.
Arguments ki_top {hAR L CS K}.
Arguments ki_mat {hAR L CS K}.

Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
Definition KAI (CS : Z -> Prop) (K : Model -> Prop) : (Z -> Prop) -> Model -> Prop :=
  fun CS' mo => K mo /\ (forall x, CS' x -> CS x).

#[using="Type"] Lemma KAI_laws : forall L CS K, kinv L CS K -> ainv_laws L (KAI CS K).
Proof.
  intros L CS K KL. split.
  - intros CS' mo [HK _]. exact (ki_halted KL mo HK).
  - intros CS' mo acc [HK HS] OK.
    ddestruct (ki_mat KL mo acc HK (acc_ok_mono L CS' CS acc HS OK)) as (mo' & E & HK' & MM).
    exists mo'. split; [exact E|]. split; [split; [exact HK'| exact HS]| exact MM].
  - intros CS1 CS2 mo HS [HK H1]. split; [exact HK|]. intros x Hx. apply H1, HS, Hx.
Qed.

Section Glue.
Variable segs : list Segment.
Variable L : asan_layout.

(* [comment removed for export] *)
End Glue.

(* [comment removed for export] *)

End ARUN_1.
