(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VMap VLin VItv VStore VFarkas VSimplex.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition itv_bot : itv := (Some 1, Some 0).

Lemma in_itv_bot x : ~ in_itv x itv_bot.
Proof. intros [H1 H2]; simpl in *; lia. Qed.

(* [comment removed for export] *)
Definition lp_component (S : store) (a : lin) : option (pmap unit * list (N * lin)) :=
  match lt a, scons S with
  | [], _ | _, [] => None
  | _, _ =>
      let '(symset, gs) := component S a in
      match gs with [] => None | _ => Some (symset, gs) end
  end.

(* [comment removed for export] *)
Definition lp_max (S : store) (symset : pmap unit) (gs : list (N * lin)) (a : lin) (bx_hi : option Z)
  : bool * option Z :=
  match lp_solve S symset gs a with
  | LOpt h => (false, meet_hi bx_hi (hint_ub S h a))
  | LInfeasible h => if is_unsat S h then (true, bx_hi) else (false, bx_hi)
  | _ => (false, bx_hi)
  end.

Definition lp_bounds (S : store) (a : lin) : itv :=
  let bx := lin_range (sbox S) a in
  match lp_component S a with
  | None => bx
  | Some (symset, gs) =>
      let '(dead1, hi) := lp_max S symset gs a (snd bx) in
      if dead1 then itv_bot else
      let '(dead2, nlo) := lp_max S symset gs (lneg a) (match fst bx with Some l => Some (- l) | None => None end) in
      if dead2 then itv_bot else
      (match nlo with Some u => Some (- u) | None => None end, hi)
  end.

(* [comment removed for export] *)
Definition lp_hi (S : store) (a : lin) : itv :=
  let bx := lin_range (sbox S) a in
  match lp_component S a with
  | None => bx
  | Some (symset, gs) =>
      let '(dead, hi) := lp_max S symset gs a (snd bx) in
      if dead then itv_bot else (fst bx, hi)
  end.

Definition lp_lo (S : store) (a : lin) : itv :=
  let bx := lin_range (sbox S) a in
  match lp_component S a with
  | None => bx
  | Some (symset, gs) =>
      let '(dead, nlo) := lp_max S symset gs (lneg a) (match fst bx with Some l => Some (- l) | None => None end) in
      if dead then itv_bot else (match nlo with Some u => Some (- u) | None => None end, snd bx)
  end.

(* [comment removed for export] *)
Section Sound.
  Variable v : val.
  Variable S : store.
  Hypothesis HS : sat v S.

  Lemma lp_max_sound symset gs a bx_hi :
    hi_ge bx_hi (eval v a) ->
    let '(dead, hi) := lp_max S symset gs a bx_hi in dead = false /\ hi_ge hi (eval v a).
  Proof.
    intros Hbx. unfold lp_max. destruct (lp_solve S symset gs a) as [h|h| |]; auto.
    - split; auto. destruct (hint_ub S h a) as [u|] eqn:E.
      + pose proof (hint_ub_sound S h a u v E HS).
        destruct bx_hi as [b|]; simpl in *; lia.
      + destruct bx_hi; simpl in *; auto.
    - destruct (is_unsat S h) eqn:E; auto.
      exfalso. exact (is_unsat_sound S h v E HS).
  Qed.

  Theorem lp_bounds_sound a : in_itv (eval v a) (lp_bounds S a).
  Proof.
    unfold lp_bounds. pose proof (sat_range v S a HS) as Hbx.
    destruct (lp_component S a) as [[symset gs]|]; auto.
    destruct Hbx as [Hlo Hhi].
    pose proof (lp_max_sound symset gs a (snd (lin_range (sbox S) a)) Hhi) as H1.
    destruct (lp_max S symset gs a _) as [d1 hi]. destruct H1 as [-> H1].
    set (nb := match fst (lin_range (sbox S) a) with Some l => Some (- l) | None => None end).
    assert (Hn : hi_ge nb (eval v (lneg a))).
    { unfold nb. rewrite eval_lneg. destruct (fst (lin_range (sbox S) a)); simpl in *; lia. }
    pose proof (lp_max_sound symset gs (lneg a) nb Hn) as H2.
    destruct (lp_max S symset gs (lneg a) nb) as [d2 nlo]. destruct H2 as [-> H2].
    split; simpl; auto.
    rewrite eval_lneg in H2. destruct nlo; simpl in *; lia.
  Qed.

  Theorem lp_hi_sound a : in_itv (eval v a) (lp_hi S a).
  Proof.
    unfold lp_hi. pose proof (sat_range v S a HS) as Hbx.
    destruct (lp_component S a) as [[symset gs]|]; auto.
    destruct Hbx as [Hlo Hhi].
    pose proof (lp_max_sound symset gs a (snd (lin_range (sbox S) a)) Hhi) as H1.
    destruct (lp_max S symset gs a _) as [d1 hi]. destruct H1 as [-> H1].
    split; auto.
  Qed.

  Theorem lp_lo_sound a : in_itv (eval v a) (lp_lo S a).
  Proof.
    unfold lp_lo. pose proof (sat_range v S a HS) as Hbx.
    destruct (lp_component S a) as [[symset gs]|]; auto.
    destruct Hbx as [Hlo Hhi].
    set (nb := match fst (lin_range (sbox S) a) with Some l => Some (- l) | None => None end).
    assert (Hn : hi_ge nb (eval v (lneg a))).
    { unfold nb. rewrite eval_lneg. destruct (fst (lin_range (sbox S) a)); simpl in *; lia. }
    pose proof (lp_max_sound symset gs (lneg a) nb Hn) as H2.
    destruct (lp_max S symset gs (lneg a) nb) as [d2 nlo]. destruct H2 as [-> H2].
    split; simpl; auto.
    rewrite eval_lneg in H2. destruct nlo; simpl in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lp_bounds_not_empty a : itv_empty (lp_bounds S a) = false.
  Proof.
    destruct (itv_empty (lp_bounds S a)) eqn:E; auto.
    exfalso. exact (itv_empty_sound _ _ E (lp_bounds_sound a)).
  Qed.
End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition add_constraint (S : store) (a : lin) : option store :=
  match lt a with
  | [] => if Z.leb (lc a) 0 then Some S else None
  | [(s, k)] => assume_single S s k (lc a)
  | _ =>
      let bx := lin_range (sbox S) a in
      if itv_lo_ge bx 1 then None else
      match lp_component S a with
      | None =>
          if itv_empty bx then None
          else if itv_hi_le bx 0 then Some S
          else assume_general S a
      | Some (symset, gs) =>
          let '(dead1, hi) := lp_max S symset gs a (snd bx) in
          if dead1 then None
          else if (match hi with Some h => Z.leb h 0 | None => false end) then Some S
          else
            let '(dead2, nlo) := lp_max S symset gs (lneg a) (match fst bx with Some l => Some (- l) | None => None end) in
            if dead2 then None
            else if (match nlo with Some u => Z.leb 1 (- u) | None => false end) then None
            else assume_general S a
      end
  end.

Theorem sat_add_constraint v S a :
  sat v S -> eval v a <= 0 ->
  exists S', add_constraint S a = Some S' /\ sat v S'.
Proof.
  intros HS Ha. unfold add_constraint.
  destruct (lt a) as [|[s k] [|t2 l2]] eqn:E.
  - rewrite (eval_is_const v a) in Ha by (unfold lin_is_const; now rewrite E).
    destruct (Z.leb_spec (lc a) 0); [eauto|lia].
  - apply sat_assume_single; auto.
    rewrite (eval_single v a s k) in Ha by (unfold lin_single; now rewrite E). lia.
  - pose proof (sat_range v S a HS) as Hbx.
    destruct (itv_lo_ge _ 1) eqn:E0.
    { exfalso. pose proof (itv_lo_ge_sound _ _ _ E0 Hbx). lia. }
    destruct (lp_component S a) as [[symset gs]|].
    + destruct Hbx as [Hlo Hhi].
      pose proof (lp_max_sound v S HS symset gs a (snd (lin_range (sbox S) a)) Hhi) as H1.
      destruct (lp_max S symset gs a _) as [d1 hi]. destruct H1 as [-> H1].
      destruct (match hi with Some h => Z.leb h 0 | None => false end) eqn:Eh; [eauto|].
      set (nb := match fst (lin_range (sbox S) a) with Some l => Some (- l) | None => None end).
      assert (Hn : hi_ge nb (eval v (lneg a))).
      { unfold nb. rewrite eval_lneg. destruct (fst (lin_range (sbox S) a)); simpl in *; lia. }
      pose proof (lp_max_sound v S HS symset gs (lneg a) nb Hn) as H2.
      destruct (lp_max S symset gs (lneg a) nb) as [d2 nlo]. destruct H2 as [-> H2].
      destruct (match nlo with Some u => Z.leb 1 (- u) | None => false end) eqn:El.
      * exfalso. destruct nlo as [u|]; [|discriminate]. apply Z.leb_le in El.
        rewrite eval_lneg in H2. simpl in H2. lia.
      * apply sat_assume_general; auto.
    + destruct (itv_empty _) eqn:E1.
      { exfalso. exact (itv_empty_sound _ _ E1 Hbx). }
      destruct (itv_hi_le _ 0); [eauto|].
      apply sat_assume_general; auto.
Qed.

(* [comment removed for export] *)
Definition add_in_itv (S : store) (a : lin) (i : itv) : option store :=
  let S1 := match snd i with
            | None => Some S
            | Some hi => add_constraint S (laddc a (- hi))          (* [comment removed for export] *)
            end in
  match S1 with
  | None => None
  | Some S1 =>
      match fst i with
      | None => Some S1
      | Some lo => add_constraint S1 (laddc (lneg a) lo)           (* [comment removed for export] *)
      end
  end.

Theorem sat_add_in_itv v S a i :
  sat v S -> in_itv (eval v a) i ->
  exists S', add_in_itv S a i = Some S' /\ sat v S'.
Proof.
  intros HS [Hlo Hhi]. unfold add_in_itv.
  assert (H1 : exists S1, (match snd i with None => Some S | Some hi => add_constraint S (laddc a (- hi)) end) = Some S1 /\ sat v S1).
  { destruct (snd i) as [hi|]; [|eauto]. apply sat_add_constraint; auto. rewrite eval_laddc. simpl in Hhi. lia. }
  destruct H1 as [S1 [-> HS1]].
  destruct (fst i) as [lo|]; [|eauto]. apply sat_add_constraint; auto.
  rewrite eval_laddc, eval_lneg. simpl in Hlo. lia.
Qed.

(* [comment removed for export] *)
Definition lp_nonpos (S : store) (a : lin) : bool := itv_hi_le (lp_hi S a) 0.

Theorem lp_nonpos_sound v S a : lp_nonpos S a = true -> sat v S -> eval v a <= 0.
Proof.
  intros H HS. exact (itv_hi_le_sound _ _ _ H (lp_hi_sound v S HS a)).
Qed.

(* [comment removed for export] *)
Definition lp_dead (S : store) (a : lin) : bool := itv_empty (lp_hi S a).

Theorem lp_dead_sound v S a : lp_dead S a = true -> ~ sat v S.
Proof.
  intros H HS. exact (itv_empty_sound _ _ H (lp_hi_sound v S HS a)).
Qed.

(* [comment removed for export] *)
Lemma store_below_add_constraint S b a S' :
  store_below S b = true -> lin_below a b = true -> add_constraint S a = Some S' -> store_below S' b = true.
Proof.
  unfold add_constraint. intros H Ha.
  destruct (lt a) as [|[s k] [|t2 l2]] eqn:E.
  - destruct (Z.leb _ 0); intros X; inversion X; now subst.
  - intros X. eapply store_below_assume_single; eauto.
    pose proof (proj1 (lin_below_iff a b) Ha) as Hs. apply Hs. unfold lsyms. rewrite E. simpl; auto.
  - destruct (itv_lo_ge _ 1); [discriminate|].
    destruct (lp_component S a) as [[symset gs]|].
    + destruct (lp_max S symset gs a _) as [d1 hi]. destruct d1; [discriminate|].
      destruct (match hi with Some h => Z.leb h 0 | None => false end); [intros X; inversion X; now subst|].
      destruct (lp_max S symset gs (lneg a) _) as [d2 nlo]. destruct d2; [discriminate|].
      destruct (match nlo with Some u => Z.leb 1 (- u) | None => false end); [discriminate|].
      intros X. eapply store_below_assume_general; eauto.
    + destruct (itv_empty _); [discriminate|]. destruct (itv_hi_le _ 0); [intros X; inversion X; now subst|].
      intros X. eapply store_below_assume_general; eauto.
Qed.
