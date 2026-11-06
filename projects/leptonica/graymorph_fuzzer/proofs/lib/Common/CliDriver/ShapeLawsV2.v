(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import CatSim ShapeAlg.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require Import Spec.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP1.
Lemma t_alt2_comm : forall A B : TSet, t_eq (t_alt2 A B) (t_alt2 B A).
Proof. intros A B tr. unfold t_alt2. tauto. Qed.
End VP1.

Section VP2.
Lemma t_alt2_assoc : forall A B C : TSet, t_eq (t_alt2 (t_alt2 A B) C) (t_alt2 A (t_alt2 B C)).
Proof. intros A B C tr. unfold t_alt2. tauto. Qed.
End VP2.

Section VP3.
Lemma t_alt2_idem_eq : forall A B : TSet, t_eq A B -> t_eq (t_alt2 A B) A.
Proof. intros A B H tr. unfold t_alt2. pose proof (H tr). tauto. Qed.
End VP3.

Section VP4.
Lemma t_alt2_idem_eq_r : forall A B : TSet, t_eq A B -> t_eq (t_alt2 A B) B.
Proof. intros A B H tr. unfold t_alt2. pose proof (H tr). tauto. Qed.
End VP4.

(* [comment removed for export] *)
Section VP5.
Lemma t_alt2_absorb : forall A B : TSet, t_eq (t_alt2 A (t_alt2 A B)) (t_alt2 A B).
Proof. intros A B tr. unfold t_alt2. tauto. Qed.
End VP5.

Section VP6.
Lemma t_alt2_congr_l : forall A A' B : TSet, t_eq A A' -> t_eq (t_alt2 A B) (t_alt2 A' B).
Proof. intros A A' B H tr. unfold t_alt2. pose proof (H tr). tauto. Qed.
End VP6.

Section VP7.
Lemma t_alt2_congr_r : forall A B B' : TSet, t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A B').
Proof. intros A B B' H tr. unfold t_alt2. pose proof (H tr). tauto. Qed.
End VP7.

(* [comment removed for export] *)
Section VP8.
Lemma t_alt3_as_alt2 : forall A B C : TSet,
  t_eq (t_alt2 A (t_alt2 B C)) (t_alt2 (t_alt2 A B) C).
Proof. intros A B C. apply t_eq_sym, t_alt2_assoc. Qed.
End VP8.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP9.
Lemma t_alt2_nil_l : forall T : TSet, T [] -> t_eq (t_alt2 t_nil T) T.
Proof.
  intros T H0 tr. unfold t_alt2, t_nil. split.
  - intros [-> | H]; [exact H0 | exact H].
  - intros H. right. exact H.
Qed.
End VP9.

Section VP10.
Lemma t_alt2_nil_r : forall T : TSet, T [] -> t_eq (t_alt2 T t_nil) T.
Proof.
  intros T H0 tr. unfold t_alt2, t_nil. split.
  - intros [H | ->]; [exact H | exact H0].
  - intros H. left. exact H.
Qed.
End VP10.

(* [comment removed for export] *)
Section VP11.
Lemma t_emit_has_nil : forall evs T, t_emit evs T [].
Proof. intros evs T. unfold t_emit. left. apply is_prefix_nil. Qed.
End VP11.

Section VP12.
Lemma t_exit_has_nil : forall code fs, t_exit code fs [].
Proof. intros. unfold t_exit. apply t_emit_has_nil. Qed.
End VP12.

Section VP13.
Lemma t_alt2_has_nil_l : forall A B : TSet, A [] -> t_alt2 A B [].
Proof. intros A B H. unfold t_alt2. left. exact H. Qed.
End VP13.

(* [comment removed for export] *)
Section VP14.
Lemma t_alt2_emit_nil_l : forall (e : list event) (T : TSet),
  T [] -> t_eq (t_alt2 (t_emit e t_nil) (t_emit e T)) (t_emit e T).
Proof.
  intros e T H0 tr. unfold t_alt2, t_emit, t_nil. split.
  - intros [[Hp | (tr' & -> & ->)] | H].
    + left. exact Hp.
    + right. exists []. split; [reflexivity | exact H0].
    + exact H.
  - intros H. right. exact H.
Qed.
End VP14.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section VP15.
Lemma W_app : forall ch (a b : list byte), W ch (a ++ b) = W ch a ++ W ch b.
Proof. intros. unfold W. apply map_app. Qed.
End VP15.

Section VP16.
Lemma W_nil : forall ch, W ch [] = [].
Proof. reflexivity. Qed.
End VP16.

Section VP17.
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
End VP17.

(* [comment removed for export] *)
Section VP18.
Lemma t_alt_W_wall : forall ch (bs : list byte) (K : TSet),
  K [] -> (1 <= length bs)%nat ->
  t_eq (t_alt (fun i : wr_index bs =>
          t_emit (W ch (firstn (proj1_sig i) bs)) (t_emit (W ch (skipn (proj1_sig i) bs)) K)))
       (t_emit (W ch bs) K).
Proof. intros ch bs K HK Hnb. unfold W. apply t_alt_wall; assumption. Qed.
End VP18.

(* [comment removed for export] *)
Section VP19.
Lemma t_emit_W_nil : forall ch (T : TSet), T [] -> t_eq (t_emit (W ch []) T) T.
Proof. intros ch T H0. rewrite W_nil. apply t_emit_nil_eq. exact H0. Qed.
End VP19.

(* [comment removed for export] *)
Section VP20.
Lemma t_emit_alt2_distr : forall (e : list event) (A B : TSet),
  t_eq (t_emit e (t_alt2 A B)) (t_alt2 (t_emit e A) (t_emit e B)).
Proof.
  intros e A B tr. unfold t_emit, t_alt2. split.
  - intros [Hp | (tr' & -> & [HA | HB])].
    + left. left. exact Hp.
    + left. right. exists tr'. auto.
    + right. right. exists tr'. auto.
  - intros [[Hp | (tr' & -> & HA)] | [Hp | (tr' & -> & HB)]].
    + left. exact Hp.
    + right. exists tr'. auto.
    + left. exact Hp.
    + right. exists tr'. auto.
Qed.
End VP20.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section VP21.
Lemma exit_code_and_255 : forall c, (0 <= c < 256)%Z ->
  bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) = exit_code c.
Proof.
  intros c Hc. unfold exit_code. apply bv_eq.
  rewrite bv_and_unsigned, !Z_to_bv_unsigned.
  rewrite !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
End VP21.

(* [comment removed for export] *)
Section VP22.
Lemma t_die_unfold : forall msg fs, t_die msg fs = t_emit (W 2 msg) (t_exit (exit_code 2) fs).
Proof. reflexivity. Qed.
End VP22.

(* [comment removed for export] *)
Section VP23.
Lemma exit_leaf_eq : forall c fs, (0 <= c < 256)%Z ->
  t_eq (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) fs)) (t_exit (exit_code c) fs).
Proof.
  intros c fs Hc. rewrite exit_code_and_255 by exact Hc. apply t_emit_W_nil. apply t_exit_has_nil.
Qed.
End VP23.
