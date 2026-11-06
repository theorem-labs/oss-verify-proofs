(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Export Od_tables.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition AT_SOWN : Z := 145568.
Definition AT_SOW : Z := 145888.
Definition AT_FIN : Z := 143712.

Lemma asown_image : ro_bytes_b asegs AT_SOWN (zbytes OD_SOWN_TAB) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asow_image : ro_bytes_b asegs AT_SOW (zbytes OD_SOW_TAB) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma afin_image : ro_bytes_b asegs AT_FIN (zbytes OD_FIN_TAB) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma abytes_at : forall A tab m, ro_bytes_b asegs A (zbytes tab) = true -> 0 <= A -> A + Z.of_nat (length tab) <= 2^64 ->
  mem_inv asegs m -> bytes_at asegs m A (zbytes tab).
Proof.
  intros A tab m TI A0 A1 MI. apply ro_bytes_at; [exact MI| exact A0| rewrite zbytes_length; exact A1|].
  apply ro_bytes_b_sound. exact TI.
Qed.
Lemma asown_at : forall m, mem_inv asegs m -> bytes_at asegs m AT_SOWN (zbytes OD_SOWN_TAB).
Proof. intros m MI. apply abytes_at; [exact asown_image| unfold AT_SOWN; lia| unfold AT_SOWN; cbn; lia| exact MI]. Qed.
Lemma asow_at : forall m, mem_inv asegs m -> bytes_at asegs m AT_SOW (zbytes OD_SOW_TAB).
Proof. intros m MI. apply abytes_at; [exact asow_image| unfold AT_SOW; lia| unfold AT_SOW; cbn; lia| exact MI]. Qed.
Lemma afin_at : forall m, mem_inv asegs m -> bytes_at asegs m AT_FIN (zbytes OD_FIN_TAB).
Proof. intros m MI. apply abytes_at; [exact afin_image| unfold AT_FIN; lia| unfold AT_FIN; cbn; lia| exact MI]. Qed.

Lemma abyte_read : forall (m : word -> option byte) A tab c, bytes_at asegs m A (zbytes tab) -> 0 <= c < Z.of_nat (length tab) ->
  ov_read_bytes asegs m (wa (A + c)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat c) tab 0)].
Proof.
  intros m A tab c H Hc. eapply (u8ro_read asegs m A (zbytes tab) c); [exact H| | lia | reflexivity].
  apply nth_error_zbytes. lia.
Qed.
Lemma asown_read : forall (m : word -> option byte) c, mem_inv asegs m -> 0 <= c < 256 ->
  ov_read_bytes asegs m (wa (AT_SOWN + c)) 1 = Some [Z_to_bv 8 (osown c)].
Proof. intros m c MI Hc. apply abyte_read; [apply asown_at; exact MI| change (length OD_SOWN_TAB) with 256%nat; lia]. Qed.
Lemma asow_read : forall (m : word -> option byte) c, mem_inv asegs m -> 0 <= c < 256 ->
  ov_read_bytes asegs m (wa (AT_SOW + c)) 1 = Some [Z_to_bv 8 (osow c)].
Proof. intros m c MI Hc. apply abyte_read; [apply asow_at; exact MI| change (length OD_SOW_TAB) with 256%nat; lia]. Qed.
Lemma afin_read : forall (m : word -> option byte) c, mem_inv asegs m -> 0 <= c < 256 ->
  ov_read_bytes asegs m (wa (AT_FIN + c)) 1 = Some [Z_to_bv 8 (ofin c)].
Proof. intros m c MI Hc. apply abyte_read; [apply afin_at; exact MI| change (length OD_FIN_TAB) with 256%nat; lia]. Qed.
