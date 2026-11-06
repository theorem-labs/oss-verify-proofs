(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import CatSim ShapeAlg Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma t_alt2_congr_r : forall A B B' : TSet, t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A B').
Proof. intros A B B' H tr. unfold t_alt2. pose proof (H tr). tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_emit_has_nil : forall evs T, t_emit evs T [].
Proof. intros evs T. unfold t_emit. left. apply is_prefix_nil. Qed.

Lemma t_exit_has_nil : forall code fs, t_exit code fs [].
Proof. intros. unfold t_exit. apply t_emit_has_nil. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma W_app : forall ch (a b : list byte), W ch (a ++ b) = W ch a ++ W ch b.
Proof. intros. unfold W. apply map_app. Qed.

Lemma W_nil : forall ch, W ch [] = [].
Proof. reflexivity. Qed.

Lemma t_emit_W_app : forall ch (a b : list byte) (T : TSet),
  t_eq (t_emit (W ch a) (t_emit (W ch b) T)) (t_emit (W ch (a ++ b)) T).
Proof.
  intros ch a b T. rewrite W_app. apply t_eq_sym.
  (* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_emit_W_nil : forall ch (T : TSet), T [] -> t_eq (t_emit (W ch []) T) T.
Proof. intros ch T H0. rewrite W_nil. apply t_emit_nil_eq. exact H0. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma exit_code_and_255 : forall c, (0 <= c < 256)%Z ->
  bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) = exit_code c.
Proof.
  intros c Hc. unfold exit_code. apply bv_eq.
  rewrite bv_and_unsigned, !Z_to_bv_unsigned.
  rewrite !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma exit_leaf_eq : forall c fs, (0 <= c < 256)%Z ->
  t_eq (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) fs)) (t_exit (exit_code c) fs).
Proof.
  intros c fs Hc. rewrite exit_code_and_255 by exact Hc. apply t_emit_W_nil. apply t_exit_has_nil.
Qed.
