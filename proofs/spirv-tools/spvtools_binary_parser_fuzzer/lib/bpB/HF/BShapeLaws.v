(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BCatSim BShapeAlg BSpec.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma t_emit_has_nil : forall evs T, t_emit evs T [].
Proof. intros evs T. unfold t_emit. left. apply is_prefix_nil. Qed.

Lemma t_exit_has_nil : forall code fs, t_exit code fs [].
Proof. intros. unfold t_exit. apply t_emit_has_nil. Qed.

Lemma t_alt2_has_nil_l : forall A B : TSet, A [] -> t_alt2 A B [].
Proof. intros A B H. unfold t_alt2. left. exact H. Qed.

Lemma W_app : forall ch (a b : list byte), W ch (a ++ b) = W ch a ++ W ch b.
Proof. intros. unfold W. apply map_app. Qed.

Lemma W_nil : forall ch, W ch [] = [].
Proof. reflexivity. Qed.

Lemma t_emit_W_app : forall ch (a b : list byte) (T : TSet),
  t_eq (t_emit (W ch a) (t_emit (W ch b) T)) (t_emit (W ch (a ++ b)) T).
Proof.
  intros ch a b T. rewrite W_app. apply t_eq_sym.

  intros tr. unfold t_emit. split.
  - intros [Hp | (tr' & -> & HT)].
    + apply is_prefix_app_split in Hp as [Hp | (b' & -> & Hp)].
      * left. exact Hp.
      * right. exists b'. split; [reflexivity | left; exact Hp].
    + right. exists (W ch b ++ tr'). split; [rewrite app_assoc; reflexivity|].
      right. exists tr'. auto.
  - intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. apply is_prefix_app_mono. exact Hp.
    + right. exists tr''. rewrite app_assoc. auto.
Qed.

Lemma t_emit_W_nil : forall ch (T : TSet), T [] -> t_eq (t_emit (W ch []) T) T.
Proof. intros ch T H0. rewrite W_nil. apply t_emit_nil_eq. exact H0. Qed.

Lemma exit_code_and_255 : forall c, (0 <= c < 256)%Z ->
  bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) = exit_code c.
Proof.
  intros c Hc. unfold exit_code. apply bv_eq.
  rewrite bv_and_unsigned, !Z_to_bv_unsigned.
  rewrite !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

