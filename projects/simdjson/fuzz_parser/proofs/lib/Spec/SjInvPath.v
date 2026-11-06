(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjStage1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Inductive bpath (data : list Z) (len : Z) : Z -> Z -> Prop :=
| bp_here : forall p, 0 <= p < len -> byte_at data p = 34 -> bpath data len p p
| bp_esc : forall p j, 0 <= p < len -> byte_at data p = 92 -> bpath data len (p + 2) j -> bpath data len p j
| bp_step : forall p j, 0 <= p < len -> byte_at data p <> 34 -> byte_at data p <> 92 -> bpath data len (p + 1) j -> bpath data len p j.

Lemma bpath_bound : forall data len p j, bpath data len p j -> p <= j < len /\ byte_at data j = 34.
Proof. induction 1; lia. Qed.

Lemma byte_at_past : forall data i, Z.of_nat (length data) <= i -> byte_at data i = 0.
Proof. intros data i H. unfold byte_at. apply nth_overflow. lia. Qed.

Lemma is_cont_not_special : forall c, is_cont c = true -> c <> 34 /\ c <> 92 /\ c <> 0.
Proof.
  intros c H. unfold is_cont in H. apply Z.eqb_eq in H.
  repeat split; intros ->; vm_compute in H; discriminate.
Qed.

Lemma is_cont_inside : forall data i, 0 <= i -> is_cont (byte_at data i) = true -> i < Z.of_nat (length data).
Proof.
  intros data i Hi H. destruct (Z_lt_ge_dec i (Z.of_nat (length data))) as [L|G]; [exact L|].
  rewrite (byte_at_past data i) in H by lia. vm_compute in H. discriminate.
Qed.

Lemma ge128_not_special : forall c, (128 <=? c) = true -> c <> 34 /\ c <> 92.
Proof. intros c H. apply Z.leb_le in H. lia. Qed.

(* [comment removed for export] *)
Lemma utf8_char_path : forall data i i' e j,
  let len := Z.of_nat (length data) in
  0 <= i < len -> (128 <=? byte_at data i) = true ->
  utf8_char data len i = (i', e) -> bpath data len i' j -> bpath data len i j.
Proof.
  intros data i i' e j len Hi H128 HU HP.
  destruct (ge128_not_special _ H128) as [N34 N92].
  unfold utf8_char in HU.
  assert (S1 : forall q, bpath data len (i + 1) q -> bpath data len i q) by (intros q Hq; apply bp_step; auto).
  assert (SK : forall k q, 0 <= k -> is_cont (byte_at data (i + k)) = true -> bpath data len (i + k + 1) q -> bpath data len (i + k) q).
  { intros k q Hk Hc Hq. destruct (is_cont_not_special _ Hc) as (A & B & _).
    apply bp_step; auto. split; [lia|]. apply is_cont_inside; [lia| exact Hc]. }
  repeat match type of HU with
         | (if ?c then _ else _) = _ => let E := fresh "E" in destruct c eqn:E
         end; inversion HU; subst i'; clear HU; try (apply S1; exact HP);
  repeat match goal with
         | H : (_ || _) = false |- _ => apply orb_false_elim in H; destruct H
         | H : negb _ = false |- _ => apply negb_false_iff in H
         end.
  - apply S1. replace (i + 1) with (i + 1 + 0) by lia. replace (i + 1 + 0) with (i + 1) by lia.
    apply (SK 1 j); [lia| assumption|]. replace (i + 1 + 1) with (i + 2) by lia. exact HP.
  - apply S1. apply (SK 1 j); [lia| assumption|]. replace (i + 1 + 1) with (i + 2) by lia.
    apply (SK 2 j); [lia| assumption|]. replace (i + 2 + 1) with (i + 3) by lia. exact HP.
  - apply S1. apply (SK 1 j); [lia| assumption|]. replace (i + 1 + 1) with (i + 2) by lia.
    apply (SK 2 j); [lia| assumption|]. replace (i + 2 + 1) with (i + 3) by lia.
    apply (SK 3 j); [lia| assumption|]. replace (i + 3 + 1) with (i + 4) by lia. exact HP.
Qed.

Theorem vstring_bpath : forall fuel data p err j e,
  let len := Z.of_nat (length data) in
  0 <= p -> vstring fuel data len p err = (Some j, e) -> bpath data len p j.
Proof.
  induction fuel as [|f IH]; intros data p err j e len Hp H; cbn [vstring] in H; [discriminate|].
  fold len in H.
  destruct (len <=? p) eqn:EL; [discriminate|]. apply Z.leb_gt in EL.
  destruct (negb (is_ascii_stop (byte_at data p))) eqn:ES.
  - (* [comment removed for export] *)
    apply negb_true_iff in ES. unfold is_ascii_stop in ES.
    repeat (apply orb_false_elim in ES; destruct ES as [ES ?]).
    apply bp_step; [lia| | |eapply IH; [lia| exact H]].
    + intros E. rewrite E in *. discriminate.
    + intros E. rewrite E in *. discriminate.
  - destruct (byte_at data p =? 34) eqn:EQ.
    + inversion H; subst. apply bp_here; [lia| apply Z.eqb_eq; exact EQ].
    + destruct (byte_at data p =? 92) eqn:EB.
      * apply bp_esc; [lia| apply Z.eqb_eq; exact EB| eapply IH; [lia| exact H]].
      * destruct (128 <=? byte_at data p) eqn:E8.
        -- destruct (utf8_char data len p) as [i' e'] eqn:EU.
           assert (Hi' : 0 <= i').
           { unfold utf8_char in EU.
             repeat match type of EU with (if ?c then _ else _) = _ => destruct c end; inversion EU; lia. }
           eapply utf8_char_path; [lia| exact E8| exact EU| eapply IH; [exact Hi'| exact H]].
        -- apply bp_step; [lia| apply Z.eqb_neq; exact EQ| apply Z.eqb_neq; exact EB| eapply IH; [lia| exact H]].
Qed.

