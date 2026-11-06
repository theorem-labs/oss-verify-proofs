(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Export Od_tables.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition UT_SOWN : Z := 79848.
Definition UT_SOW : Z := 80104.
Definition UT_FIN : Z := 78128.

Lemma usown_image : ro_bytes_b usegs UT_SOWN (zbytes OD_SOWN_TAB) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma usow_image : ro_bytes_b usegs UT_SOW (zbytes OD_SOW_TAB) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ufin_image : ro_bytes_b usegs UT_FIN (zbytes OD_FIN_TAB) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ubytes_at : forall A tab m, ro_bytes_b usegs A (zbytes tab) = true -> 0 <= A -> A + Z.of_nat (length tab) <= 2^64 ->
  mem_inv usegs m -> bytes_at usegs m A (zbytes tab).
Proof.
  intros A tab m TI A0 A1 MI. apply ro_bytes_at; [exact MI| exact A0| rewrite zbytes_length; exact A1|].
  apply ro_bytes_b_sound. exact TI.
Qed.
Lemma usown_at : forall m, mem_inv usegs m -> bytes_at usegs m UT_SOWN (zbytes OD_SOWN_TAB).
Proof. intros m MI. apply ubytes_at; [exact usown_image| unfold UT_SOWN; lia| unfold UT_SOWN; cbn; lia| exact MI]. Qed.
Lemma usow_at : forall m, mem_inv usegs m -> bytes_at usegs m UT_SOW (zbytes OD_SOW_TAB).
Proof. intros m MI. apply ubytes_at; [exact usow_image| unfold UT_SOW; lia| unfold UT_SOW; cbn; lia| exact MI]. Qed.
Lemma ufin_at : forall m, mem_inv usegs m -> bytes_at usegs m UT_FIN (zbytes OD_FIN_TAB).
Proof. intros m MI. apply ubytes_at; [exact ufin_image| unfold UT_FIN; lia| unfold UT_FIN; cbn; lia| exact MI]. Qed.

Lemma ubyte_read : forall (m : word -> option byte) A tab c, bytes_at usegs m A (zbytes tab) -> 0 <= c < Z.of_nat (length tab) ->
  ov_read_bytes usegs m (wa (A + c)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat c) tab 0)].
Proof.
  intros m A tab c H Hc. eapply (u8ro_read usegs m A (zbytes tab) c); [exact H| | lia | reflexivity].
  apply nth_error_zbytes. lia.
Qed.
Lemma usown_read : forall (m : word -> option byte) c, mem_inv usegs m -> 0 <= c < 256 ->
  ov_read_bytes usegs m (wa (UT_SOWN + c)) 1 = Some [Z_to_bv 8 (osown c)].
Proof. intros m c MI Hc. apply ubyte_read; [apply usown_at; exact MI| change (length OD_SOWN_TAB) with 256%nat; lia]. Qed.
Lemma usow_read : forall (m : word -> option byte) c, mem_inv usegs m -> 0 <= c < 256 ->
  ov_read_bytes usegs m (wa (UT_SOW + c)) 1 = Some [Z_to_bv 8 (osow c)].
Proof. intros m c MI Hc. apply ubyte_read; [apply usow_at; exact MI| change (length OD_SOW_TAB) with 256%nat; lia]. Qed.
Lemma ufin_read : forall (m : word -> option byte) c, mem_inv usegs m -> 0 <= c < 256 ->
  ov_read_bytes usegs m (wa (UT_FIN + c)) 1 = Some [Z_to_bv 8 (ofin c)].
Proof. intros m c MI Hc. apply ubyte_read; [apply ufin_at; exact MI| change (length OD_FIN_TAB) with 256%nat; lia]. Qed.
