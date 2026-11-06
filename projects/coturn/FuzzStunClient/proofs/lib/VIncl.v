(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VMap VLin VItv VStore VFarkas VCong VSimplex VBounds.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition round_hi (S : store) (e : lin) (u : Z) : Z :=
  let '(m, r) := lin_cong (scong S) e in if Z.ltb 1 m then floor_to_class m r u else u.
Definition round_lo (S : store) (e : lin) (l : Z) : Z :=
  let '(m, r) := lin_cong (scong S) e in if Z.ltb 1 m then ceil_to_class m r l else l.

(* [comment removed for export] *)
Definition check_hi (S : store) (e : lin) (hi : Z) : bool :=
  if itv_hi_le (lin_range (sbox S) e) hi then true else
  (let b := lp_hi S e in
      if (if itv_empty b then true else itv_hi_le b hi) then true else
      match snd b with Some u => Z.leb (round_hi S e u) hi | None => false end).

Lemma check_hi_orb S e hi : check_hi S e hi =
  (itv_hi_le (lin_range (sbox S) e) hi
   || (let b := lp_hi S e in
       itv_empty b || itv_hi_le b hi
       || match snd b with Some u => Z.leb (round_hi S e u) hi | None => false end)).
Proof. reflexivity. Qed.

Definition check_lo (S : store) (e : lin) (lo : Z) : bool :=
  if itv_lo_ge (lin_range (sbox S) e) lo then true else
  (let b := lp_lo S e in
      if (if itv_empty b then true else itv_lo_ge b lo) then true else
      match fst b with Some l => Z.leb lo (round_lo S e l) | None => false end).

Lemma check_lo_orb S e lo : check_lo S e lo =
  (itv_lo_ge (lin_range (sbox S) e) lo
   || (let b := lp_lo S e in
       itv_empty b || itv_lo_ge b lo
       || match fst b with Some l => Z.leb lo (round_lo S e l) | None => false end)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition store_dead (S : store) : bool :=
  if existsb_l (fun si : positive * itv => itv_empty (snd si)) (pm_elements (sbox S)) then true
  else existsb_l (fun c => lp_dead S c) (scons S).

Lemma store_dead_orb S : store_dead S =
  (existsb (fun si : positive * itv => itv_empty (snd si)) (pm_elements (sbox S))
   || existsb (fun c => lp_dead S c) (scons S)).
Proof. unfold store_dead. rewrite !existsb_l_eq. reflexivity. Qed.

Theorem store_dead_sound v S : store_dead S = true -> ~ sat v S.
Proof.
  rewrite store_dead_orb. intros H HS. apply orb_prop in H. destruct H as [H|H].
  - apply existsb_exists in H as [[s i] [Hin He]]. cbn [snd] in He.
    apply pm_elements_sound in Hin. exact (itv_empty_sound _ _ He (sat_box v S HS s i Hin)).
  - apply existsb_exists in H as [c [Hin Hd]]. exact (lp_dead_sound v S c Hd HS).
Qed.

Definition check_in_itv (S : store) (e : lin) (i : itv) : bool :=
  if (match snd i with None => true | Some hi => check_hi S e hi end)
  then (match fst i with None => true | Some lo => check_lo S e lo end) else false.

Lemma check_in_itv_andb S e i : check_in_itv S e i =
  ((match snd i with None => true | Some hi => check_hi S e hi end)
   && (match fst i with None => true | Some lo => check_lo S e lo end)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition check_nonpos (S : store) (e : lin) : bool := check_hi S e 0.

(* [comment removed for export] *)
Definition check_in_itv_f (S : store) (e : lin) (i : itv) : bool :=
  match e with
  | mkLin Z0 [(s, Zpos xH)] => if itv_le (box_get (sbox S) s) i then true else check_in_itv S e i
  | _ => check_in_itv S e i
  end.

Lemma lin_range_bare B s : lin_range B (mkLin 0 [(s, 1)]) = box_get B s.
Proof.
  unfold lin_range. cbn [lt lc terms_range]. destruct (box_get B s) as [[[|l|l]|] [[|h|h]|]]; reflexivity.
Qed.

Lemma check_in_itv_f_eq S e i : check_in_itv_f S e i = check_in_itv S e i.
Proof.
  unfold check_in_itv_f. destruct e as [c l]. destruct c; try reflexivity.
  destruct l as [|[s k] t]; try reflexivity. destruct k as [|[k|k|]|k]; try reflexivity. destruct t; try reflexivity.
  destruct (itv_le (box_get (sbox S) s) i) eqn:E; [|reflexivity].
  symmetry. unfold check_in_itv, check_hi, check_lo. rewrite lin_range_bare.
  unfold itv_le in E. apply andb_prop in E as [E1 E2].
  destruct i as [[lo|] [hi|]]; cbn [fst snd] in *.
  - unfold itv_hi_le, itv_lo_ge. destruct (box_get (sbox S) s) as [[bl|] [bh|]]; cbn [fst snd] in *; try discriminate.
    rewrite E1, E2. reflexivity.
  - unfold itv_lo_ge. destruct (box_get (sbox S) s) as [[bl|] bh]; cbn [fst snd] in *; try discriminate.
    rewrite E1. reflexivity.
  - unfold itv_hi_le. destruct (box_get (sbox S) s) as [bl [bh|]]; cbn [fst snd] in *; try discriminate.
    rewrite E2. reflexivity.
  - reflexivity.
Qed.
#[global] Arguments check_in_itv_f : simpl never.

Lemma forallb_l_ext {A : Type} (f g : A -> bool) (l : list A) : (forall x, f x = g x) -> forallb_l f l = forallb_l g l.
Proof. intros H. induction l as [|x t IH]; cbn [forallb_l]; [reflexivity|]. rewrite H, IH. reflexivity. Qed.

Definition subst_sym (sigma : pmap lin) (s : sym) : lin :=
  match pm_get s sigma with Some e => e | None => lsym s end.

Definition store_entails (S : store) (sigma : pmap lin) (S' : store) : bool :=
  if (if pm_forallb_l (fun s i => check_in_itv_f S (subst_sym sigma s) i) (sbox S')
      then forallb_l (fun c => check_nonpos S (lsubst sigma c)) (scons S') else false)
  then pm_forallb_l (fun s mr => entails_cong (scong S) (subst_sym sigma s) (fst mr) (snd mr)) (scong S') else false.

Lemma store_entails_andb S sigma S' : store_entails S sigma S' =
  (pm_forallb (fun s i => check_in_itv S (subst_sym sigma s) i) (sbox S')
   && forallb (fun c => check_nonpos S (lsubst sigma c)) (scons S')
   && pm_forallb (fun s mr => entails_cong (scong S) (subst_sym sigma s) (fst mr) (snd mr)) (scong S')).
Proof.
  unfold store_entails.
  replace (pm_forallb_l (fun s i => check_in_itv_f S (subst_sym sigma s) i) (sbox S'))
    with (pm_forallb_l (fun s i => check_in_itv S (subst_sym sigma s) i) (sbox S'))
    by (unfold pm_forallb_l; apply forallb_l_ext; intros x; symmetry; apply check_in_itv_f_eq).
  rewrite !pm_forallb_l_eq, forallb_l_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Section Sound.
  Variable v : val.
  Variable S : store.
  Hypothesis HS : sat v S.

  Lemma round_hi_sound e u : eval v e <= u -> eval v e <= round_hi S e u.
  Proof.
    intros Hu. unfold round_hi.
    pose proof (lin_cong_sound v (scong S) e (sat_cong v S HS)) as HC.
    destruct (lin_cong (scong S) e) as [m r]. destruct HC as (Hd&_).
    destruct (Z.ltb_spec 1 m); [|exact Hu]. apply floor_to_class_ge; auto. lia.
  Qed.

  Lemma round_lo_sound e l : l <= eval v e -> round_lo S e l <= eval v e.
  Proof.
    intros Hl. unfold round_lo.
    pose proof (lin_cong_sound v (scong S) e (sat_cong v S HS)) as HC.
    destruct (lin_cong (scong S) e) as [m r]. destruct HC as (Hd&_).
    destruct (Z.ltb_spec 1 m); [|exact Hl]. apply ceil_to_class_le; auto. lia.
  Qed.

  Lemma check_hi_sound e hi : check_hi S e hi = true -> eval v e <= hi.
  Proof.
    rewrite check_hi_orb. intros H. apply orb_prop in H as [H|H].
    - exact (itv_hi_le_sound _ _ _ H (sat_range v S e HS)).
    - pose proof (lp_hi_sound v S HS e) as Hb. apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
      + exfalso. exact (itv_empty_sound _ _ H Hb).
      + exact (itv_hi_le_sound _ _ _ H Hb).
      + destruct (lp_hi S e) as [bl [u|]]; [|discriminate]. cbn [snd] in H. apply Z.leb_le in H.
        destruct Hb as [_ Hu]. cbn [snd hi_ge] in Hu. pose proof (round_hi_sound e u Hu). lia.
  Qed.

  Lemma check_lo_sound e lo : check_lo S e lo = true -> lo <= eval v e.
  Proof.
    rewrite check_lo_orb. intros H. apply orb_prop in H as [H|H].
    - exact (itv_lo_ge_sound _ _ _ H (sat_range v S e HS)).
    - pose proof (lp_lo_sound v S HS e) as Hb. apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
      + exfalso. exact (itv_empty_sound _ _ H Hb).
      + exact (itv_lo_ge_sound _ _ _ H Hb).
      + destruct (lp_lo S e) as [[l|] bh]; [|discriminate]. cbn [fst] in H. apply Z.leb_le in H.
        destruct Hb as [Hl _]. cbn [fst lo_le] in Hl. pose proof (round_lo_sound e l Hl). lia.
  Qed.

  Lemma check_in_itv_sound e i : check_in_itv S e i = true -> in_itv (eval v e) i.
  Proof.
    rewrite check_in_itv_andb. intros H. apply andb_prop in H as [H1 H2].
    destruct i as [[lo|] [hi|]]; simpl in *; split; simpl;
      auto using check_hi_sound, check_lo_sound; exact I.
  Qed.

  Lemma check_nonpos_sound e : check_nonpos S e = true -> eval v e <= 0.
  Proof. apply check_hi_sound. Qed.

  Lemma eval_subst_sym sigma s : eval v (subst_sym sigma s) = vsubst v sigma s.
  Proof.
    unfold subst_sym, vsubst. destruct (pm_get s sigma); [reflexivity|apply eval_lsym].
  Qed.

  Theorem store_entails_sound sigma S' :
    store_entails S sigma S' = true -> sat (vsubst v sigma) S'.
  Proof.
    rewrite store_entails_andb. intros H.
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    split; [|split].
    - intros s i Hg. pose proof (pm_forallb_sound _ _ H1 s Hg) as Hc. simpl in Hc.
      rewrite <- eval_subst_sym. now apply check_in_itv_sound.
    - rewrite Forall_forall. intros c Hin. rewrite forallb_forall in H2. specialize (H2 _ Hin).
      rewrite <- eval_lsubst. now apply check_nonpos_sound.
    - intros s m r Hg. pose proof (pm_forallb_sound _ _ H3 s Hg) as Hc. simpl in Hc.
      rewrite <- eval_subst_sym. apply entails_cong_sound with (C := scong S); auto.
      now apply sat_cong.
  Qed.
End Sound.

(* [comment removed for export] *)
Definition store_le (S S' : store) : bool := store_entails S pm_empty S'.

Lemma vsubst_empty v s : vsubst v pm_empty s = v s.
Proof. unfold vsubst. now rewrite pm_get_empty. Qed.

Theorem store_le_sound S S' v : store_le S S' = true -> sat v S -> sat v S'.
Proof.
  intros H HS. apply sat_ext with (vsubst v pm_empty).
  - intros; apply vsubst_empty.
  - eapply store_entails_sound; eauto.
Qed.
