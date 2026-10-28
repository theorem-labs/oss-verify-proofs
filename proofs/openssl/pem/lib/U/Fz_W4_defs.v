(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Arr SFModel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ectx_cells (num : word) (ed : list byte) (ln fl : word) : list cell := [C4 num; CB 80 ed; C4 ln; C4 fl].

(* [comment removed for export] *)
Notation B64_TABLE := (0x58ccc)%Z (only parsing).
Definition b64_table : list byte :=
  Eval vm_compute in (match image_bytes usegs 0x58ccc 128 with Some bs => bs | None => [] end).

Lemma b64_table_len : length b64_table = 128%nat.
Proof. reflexivity. Qed.

Lemma b64_table_at : forall m, mem_inv usegs m -> bytes_at usegs m B64_TABLE b64_table.
Proof.
  intros m HI.
  assert (RO : ro_cells usegs m B64_TABLE [CB 128 b64_table])
    by (apply (ro_cells_image usegs m B64_TABLE b64_table HI); [vm_compute; reflexivity | lia | cbn; lia]).
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

(* [comment removed for export] *)
Lemma b64_table_nth : forall c, 0 <= c < 128 -> exists v, nth_error b64_table (Z.to_nat c) = Some v.
Proof.
  intros c Hc. destruct (nth_error b64_table (Z.to_nat c)) as [v|] eqn:E; [exists v; reflexivity|].
  apply nth_error_None in E. rewrite b64_table_len in E. lia.
Qed.

(* [comment removed for export] *)
Lemma byte_signed : forall b : byte, bv_signed b = if bv_unsigned b <? 128 then bv_unsigned b else bv_unsigned b - 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 8) with 256. change (256 / 2) with 128.
  destruct (Z.ltb_spec (bv_unsigned b) 128).
  - rewrite Z.mod_small by lia. lia.
  - replace (bv_unsigned b + 128) with (bv_unsigned b - 128 + 1 * 256) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma sxb_cases : forall b : byte,
  (bv_lts (sxb b) (Z_to_bv 64 0) = true /\ 128 <= bv_unsigned b)
  \/ (bv_lts (sxb b) (Z_to_bv 64 0) = false /\ bv_unsigned b < 128 /\ sxb b = Z_to_bv 64 (bv_unsigned b)).
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
  unfold bv_lts, sxb. rewrite (byte_signed b).
  assert (S0 : bv_signed (Z_to_bv 64 0) = 0) by (apply SFModel.signed_of_Z; lia). rewrite S0.
  destruct (Z.ltb_spec (bv_unsigned b) 128).
  - right. rewrite SFModel.signed_of_Z by lia. split; [apply Z.ltb_ge; lia|]. split; [lia | reflexivity].
  - left. rewrite SFModel.signed_of_Z by lia. split; [apply Z.ltb_lt; lia | lia].
Qed.

(* [comment removed for export] *)
Lemma t_le1_word : forall w : word, le1 w = [Z_to_bv 8 (bv_unsigned w mod 256)].
Proof. intros w. rewrite <- (Z_to_bv_bv_unsigned w) at 1. apply th_le1_mod. Qed.

(* [comment removed for export] *)
Lemma ro_cells_congr : forall segs m A cs cs',
  cells_bytes cs = cells_bytes cs' -> cells_wf cs' -> ro_cells segs m A cs -> ro_cells segs m A cs'.
Proof. intros segs m A cs cs' EB WF [_ B]. split; [exact WF | rewrite <- EB; exact B]. Qed.

(* [comment removed for export] *)
Lemma ectx_data : forall m C num ed ln fl, length ed = 80%nat ->
  ro_cells usegs m C (ectx_cells num ed ln fl) -> bytes_at usegs m (C + 4) ed.
Proof.
  intros m C num ed ln fl L [_ B]. unfold ectx_cells in B. cbn [cells_bytes cbytes] in B.
  apply bytes_at_app in B. destruct B as [_ B]. apply bytes_at_app in B. destruct B as [B _].
  replace (Z.of_nat (length (le4 num))) with 4 in B by reflexivity. exact B.
Qed.
