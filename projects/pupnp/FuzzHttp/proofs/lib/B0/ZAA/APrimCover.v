(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Finite FinFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import APrim APrimPop APrimQ.
Import ListNotations.
Open Scope Z_scope.

Definition cover (P : prim) (hs : list (Z * Z)) : Prop :=
  forall c v, 1 <= c <= 31 -> 0 <= v -> 16 * v + class_size c <= p_au (get_cls P c) -> (16 * v) mod class_size c = 0 ->
    In v (cls_free (get_cls P c)) \/ In (c, v) hs.

Lemma cover_incl : forall P hs hs', cover P hs -> incl hs hs' -> cover P hs'.
Proof. intros P hs hs' CV INC c v Hc V0 V1 V2. destruct (CV c v Hc V0 V1 V2) as [HF|HH]; [left; exact HF| right; apply INC; exact HH]. Qed.

Lemma cover_pop : forall P P' hs c v, cover P hs ->
  (forall c', c' <> c -> get_cls P' c' = get_cls P c') ->
  p_au (get_cls P' c) = p_au (get_cls P c) ->
  (forall x, In x (cls_free (get_cls P' c)) <-> In x (cls_free (get_cls P c)) /\ x <> v) ->
  cover P' ((c, v) :: hs).
Proof.
  intros P P' hs c v CV OTH AU FR c' v' Hc V0 V1 V2. destruct (Z.eq_dec c' c) as [->|NE].
  - rewrite AU in V1. destruct (CV c v' Hc V0 V1 V2) as [HF|HH].
    + destruct (Z.eq_dec v' v) as [->|NV]; [right; left; reflexivity| left; apply FR; split; assumption].
    + right; right; exact HH.
  - rewrite (OTH c' NE) in V1 |- *. destruct (CV c' v' Hc V0 V1 V2) as [HF|HH]; [left; exact HF| right; right; exact HH].
Qed.

Lemma cover_push : forall P P' hs c v, cover P hs ->
  (forall c', c' <> c -> get_cls P' c' = get_cls P c') ->
  p_au (get_cls P' c) = p_au (get_cls P c) ->
  (forall x, In x (cls_free (get_cls P' c)) <-> In x (cls_free (get_cls P c)) \/ x = v) ->
  cover P' (List.remove cv_eq_dec (c, v) hs).
Proof.
  intros P P' hs c v CV OTH AU FR c' v' Hc V0 V1 V2. destruct (Z.eq_dec c' c) as [->|NE].
  - rewrite AU in V1. destruct (CV c v' Hc V0 V1 V2) as [HF|HH].
    + left. apply FR. left. exact HF.
    + destruct (Z.eq_dec v' v) as [->|NV]; [left; apply FR; right; reflexivity|].
      right. apply in_in_remove; [intros EQ; inversion EQ; contradiction| exact HH].
  - rewrite (OTH c' NE) in V1 |- *. destruct (CV c' v' Hc V0 V1 V2) as [HF|HH]; [left; exact HF|].
    right. apply in_in_remove; [intros EQ; inversion EQ; contradiction| exact HH].
Qed.

Lemma cover_grow : forall P P' hs c, cover P hs ->
  (forall c', c' <> c -> get_cls P' c' = get_cls P c') ->
  (forall x, In x (cls_free (get_cls P c)) -> In x (cls_free (get_cls P' c))) ->
  (forall x, 0 <= x -> p_au (get_cls P c) <= 16 * x -> 16 * x + class_size c <= p_au (get_cls P' c) -> (16 * x) mod class_size c = 0 ->
             In x (cls_free (get_cls P' c))) ->
  p_au (get_cls P c) mod class_size c = 0 -> 1 <= c <= 31 ->
  cover P' hs.
Proof.
  intros P P' hs c CV OTH GROW NEW AUM Hc0 c' v' Hc V0 V1 V2. destruct (Z.eq_dec c' c) as [->|NE].
  - pose proof (class_size_pos c Hc) as CS.
    destruct (Z_lt_ge_dec (16 * v') (p_au (get_cls P c))) as [LT|GE].
    +
      assert (V1' : 16 * v' + class_size c <= p_au (get_cls P c)).
      { pose proof (Z.div_mod (16 * v') (class_size c) ltac:(lia)) as E1. pose proof (Z.div_mod (p_au (get_cls P c)) (class_size c) ltac:(lia)) as E2.
        rewrite V2 in E1. rewrite AUM in E2. clear - E1 E2 LT CS.
        set (q1 := 16 * v' / class_size c) in *. set (q2 := p_au (get_cls P c) / class_size c) in *. set (sz := class_size c) in *.
        assert (Q12 : q1 < q2) by nia. assert (Q13 : sz * (q1 + 1) <= sz * q2) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
      destruct (CV c v' Hc V0 V1' V2) as [HF|HH]; [left; apply GROW; exact HF| right; exact HH].
    + left. apply NEW; [exact V0| lia| exact V1| exact V2].
  - rewrite (OTH c' NE) in V1 |- *. exact (CV c' v' Hc V0 V1 V2).
Qed.

Definition held_cls (c : Z) (hs : list (Z * Z)) : list Z := map snd (List.filter (fun cv => fst cv =? c) hs).
Lemma cover_count : forall P hs c, cover P hs -> 1 <= c <= 31 -> 0 <= p_au (get_cls P c) -> p_au (get_cls P c) mod class_size c = 0 ->
  p_au (get_cls P c) / class_size c <= Z.of_nat (length (cls_free (get_cls P c))) + Z.of_nat (length (held_cls c hs)).
Proof.
  intros P hs c CV Hc AU0 AUM. pose proof (class_size_pos c Hc) as CS. pose proof (class_size_mod16 c Hc) as CM.
  set (sz := class_size c) in *. set (au := p_au (get_cls P c)) in *.
  set (N := Z.to_nat (au / sz)).
  set (idx := map (fun i => Z.of_nat i * (sz / 16)) (seq 0 N)).
  assert (NDI : List.NoDup idx).
  { unfold idx. apply Finite.Injective_map_NoDup; [| apply seq_NoDup]. intros i j E. assert (0 < sz / 16) by (Z.div_mod_to_equations; lia). nia. }
  assert (INC : incl idx (cls_free (get_cls P c) ++ held_cls c hs)).
  { intros x Hx. unfold idx in Hx. apply in_map_iff in Hx as (i & <- & Hi). apply in_seq in Hi.
    assert (E16 : 16 * (Z.of_nat i * (sz / 16)) = Z.of_nat i * sz) by (Z.div_mod_to_equations; nia).
    assert (IB : Z.of_nat i < au / sz) by (unfold N in Hi; lia).
    assert (AUE : au = sz * (au / sz)) by (Z.div_mod_to_equations; nia).
    destruct (CV c (Z.of_nat i * (sz / 16)) Hc ltac:(assert (0 <= sz / 16) by (Z.div_mod_to_equations; lia); nia)
                ltac:(fold sz au; rewrite E16; nia) ltac:(fold sz; rewrite E16; apply Z_mod_mult)) as [HF|HH].
    - apply in_or_app. left. exact HF.
    - apply in_or_app. right. unfold held_cls. apply in_map_iff. exists (c, Z.of_nat i * (sz / 16)). split; [reflexivity|].
      apply filter_In. split; [exact HH| cbn [fst]; apply Z.eqb_refl]. }
  pose proof (NoDup_incl_length NDI INC) as LE. unfold idx in LE. rewrite length_map, length_seq, length_app in LE.
  unfold N in LE. lia.
Qed.
