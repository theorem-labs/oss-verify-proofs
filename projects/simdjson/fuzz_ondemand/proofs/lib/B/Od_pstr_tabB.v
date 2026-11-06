(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Od_tables.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition BT_ESC : Z := 164864.
Definition BT_DIG : Z := 146304.

Lemma besc_image : ro_bytes_b bsegs BT_ESC (zbytes OD_ESCAPE_MAP) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma bdig_image : ro_bytes_b bsegs BT_DIG (u32s OD_DIGIT_WORDS) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma besc_at : forall m, mem_inv bsegs m -> bytes_at bsegs m BT_ESC (zbytes OD_ESCAPE_MAP).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold BT_ESC; lia| rewrite zbytes_length; unfold BT_ESC; cbn; lia|].
  apply ro_bytes_b_sound. exact besc_image.
Qed.
Lemma bdig_at : forall m, mem_inv bsegs m -> bytes_at bsegs m BT_DIG (u32s OD_DIGIT_WORDS).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold BT_DIG; lia | rewrite u32s_length; unfold BT_DIG, OD_DIGIT_WORDS; rewrite length_map; cbn; lia |].
  apply ro_bytes_b_sound. exact bdig_image.
Qed.

Lemma besc_read : forall (m : word -> option byte) c, mem_inv bsegs m -> 0 <= c < 256 ->
  ov_read_bytes bsegs m (wa (BT_ESC + c)) 1 = Some [Z_to_bv 8 (oesc c)].
Proof.
  intros m c MI Hc. unfold oesc.
  eapply (u8ro_read bsegs m BT_ESC (zbytes OD_ESCAPE_MAP) c); [apply besc_at; exact MI| | lia | reflexivity].
  apply nth_error_zbytes. change (length OD_ESCAPE_MAP) with 256%nat. lia.
Qed.

Lemma bu32ro_read : forall (m : word -> option byte) A ws (i : Z) w a,
  bytes_at bsegs m A (u32s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 4 * i) ->
  ov_read_bytes bsegs m a 4 = Some (le4 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (4 * i) with (Z.of_nat (4 * Z.to_nat i)) by lia.
  rewrite (bytes_at_ov_read bsegs m A (u32s ws) (4 * Z.to_nat i) 4 Hb).
  2:{ rewrite Eu, !length_app, length_le4, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
  rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma bdig_read : forall (m : word -> option byte) i a, mem_inv bsegs m -> 0 <= i < 886 -> a = wa (BT_DIG + 4 * i) ->
  ov_read_bytes bsegs m a 4 = Some (le4 (Z_to_bv 64 (odig i))).
Proof.
  intros m i a MI Hi ->. eapply (bu32ro_read m BT_DIG OD_DIGIT_WORDS i); [apply bdig_at; exact MI| | lia | reflexivity].
  unfold OD_DIGIT_WORDS, odig. rewrite nth_error_map. rewrite (nth_error_nth' OD_DIGIT_TAB 0); [reflexivity|].
  change (length OD_DIGIT_TAB) with 886%nat. lia.
Qed.
