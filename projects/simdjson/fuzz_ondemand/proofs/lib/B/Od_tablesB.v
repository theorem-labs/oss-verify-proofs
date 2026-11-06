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

Definition BT_SOWN : Z := 145664.
Definition BT_SOW : Z := 145984.
Definition BT_FIN : Z := 143808.

Lemma bsown_image : ro_bytes_b bsegs BT_SOWN (zbytes OD_SOWN_TAB) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma bsow_image : ro_bytes_b bsegs BT_SOW (zbytes OD_SOW_TAB) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma bfin_image : ro_bytes_b bsegs BT_FIN (zbytes OD_FIN_TAB) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bbytes_at : forall A tab m, ro_bytes_b bsegs A (zbytes tab) = true -> 0 <= A -> A + Z.of_nat (length tab) <= 2^64 ->
  mem_inv bsegs m -> bytes_at bsegs m A (zbytes tab).
Proof.
  intros A tab m TI A0 A1 MI. apply ro_bytes_at; [exact MI| exact A0| rewrite zbytes_length; exact A1|].
  apply ro_bytes_b_sound. exact TI.
Qed.
Lemma bsown_at : forall m, mem_inv bsegs m -> bytes_at bsegs m BT_SOWN (zbytes OD_SOWN_TAB).
Proof. intros m MI. apply bbytes_at; [exact bsown_image| unfold BT_SOWN; lia| unfold BT_SOWN; cbn; lia| exact MI]. Qed.
Lemma bsow_at : forall m, mem_inv bsegs m -> bytes_at bsegs m BT_SOW (zbytes OD_SOW_TAB).
Proof. intros m MI. apply bbytes_at; [exact bsow_image| unfold BT_SOW; lia| unfold BT_SOW; cbn; lia| exact MI]. Qed.
Lemma bfin_at : forall m, mem_inv bsegs m -> bytes_at bsegs m BT_FIN (zbytes OD_FIN_TAB).
Proof. intros m MI. apply bbytes_at; [exact bfin_image| unfold BT_FIN; lia| unfold BT_FIN; cbn; lia| exact MI]. Qed.

Lemma bbyte_read : forall (m : word -> option byte) A tab c, bytes_at bsegs m A (zbytes tab) -> 0 <= c < Z.of_nat (length tab) ->
  ov_read_bytes bsegs m (wa (A + c)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat c) tab 0)].
Proof.
  intros m A tab c H Hc. eapply (u8ro_read bsegs m A (zbytes tab) c); [exact H| | lia | reflexivity].
  apply nth_error_zbytes. lia.
Qed.
Lemma bsown_read : forall (m : word -> option byte) c, mem_inv bsegs m -> 0 <= c < 256 ->
  ov_read_bytes bsegs m (wa (BT_SOWN + c)) 1 = Some [Z_to_bv 8 (osown c)].
Proof. intros m c MI Hc. apply bbyte_read; [apply bsown_at; exact MI| change (length OD_SOWN_TAB) with 256%nat; lia]. Qed.
Lemma bsow_read : forall (m : word -> option byte) c, mem_inv bsegs m -> 0 <= c < 256 ->
  ov_read_bytes bsegs m (wa (BT_SOW + c)) 1 = Some [Z_to_bv 8 (osow c)].
Proof. intros m c MI Hc. apply bbyte_read; [apply bsow_at; exact MI| change (length OD_SOW_TAB) with 256%nat; lia]. Qed.
Lemma bfin_read : forall (m : word -> option byte) c, mem_inv bsegs m -> 0 <= c < 256 ->
  ov_read_bytes bsegs m (wa (BT_FIN + c)) 1 = Some [Z_to_bv 8 (ofin c)].
Proof. intros m c MI Hc. apply bbyte_read; [apply bfin_at; exact MI| change (length OD_FIN_TAB) with 256%nat; lia]. Qed.
