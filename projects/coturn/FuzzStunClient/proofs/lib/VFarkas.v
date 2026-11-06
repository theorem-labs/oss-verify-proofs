(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VMap VLin VItv VStore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Inductive hint : Type :=
| HBox
| HIdx (k : positive) (lams : list (N * positive))
| HLin (k : positive) (lams : list (positive * lin)).

Fixpoint list_nthN {A : Type} (l : list A) (n : N) {struct l} : option A :=
  match l with
  | [] => None
  | x :: t => if N.eqb n 0 then Some x else list_nthN t (N.pred n)
  end.

Lemma list_nthN_in {A} (l : list A) : forall n x, list_nthN l n = Some x -> In x l.
Proof.
  induction l as [|y t IH]; intros n x H; simpl in *; [discriminate|].
  destruct (N.eqb n 0); [inversion H; auto| right; eauto].
Qed.

Fixpoint comb_idx (cs : list lin) (lams : list (N * positive)) (acc : lin) : option lin :=
  match lams with
  | [] => Some acc
  | (i, lam) :: t =>
      match list_nthN cs i with
      | None => None
      | Some c => comb_idx cs t (laxpy acc (Zneg lam) c)
      end
  end.

Fixpoint comb_lin (cs : list lin) (lams : list (positive * lin)) (acc : lin) : option lin :=
  match lams with
  | [] => Some acc
  | (lam, c) :: t =>
      if lin_mem c cs then comb_lin cs t (laxpy acc (Zneg lam) c) else None
  end.

Definition hint_k (h : hint) : positive :=
  match h with HBox => 1%positive | HIdx k _ => k | HLin k _ => k end.

Definition hint_residual (S : store) (h : hint) (a : lin) : option lin :=
  match h with
  | HBox => Some a
  | HIdx k lams => comb_idx (scons S) lams (lscale (Zpos k) a)
  | HLin k lams => comb_lin (scons S) lams (lscale (Zpos k) a)
  end.

(* [comment removed for export] *)
Definition entails_nonpos (S : store) (h : hint) (a : lin) : bool :=
  match hint_residual S h a with
  | None => false
  | Some r => itv_hi_lt (lin_range (sbox S) r) (Zpos (hint_k h))
  end.

(* [comment removed for export] *)
Section Soundness.
  Variable v : val.

  Lemma comb_idx_ge cs : Forall (fun c => eval v c <= 0) cs ->
    forall lams acc r, comb_idx cs lams acc = Some r -> eval v acc <= eval v r.
  Proof.
    intros Hcs lams. induction lams as [|[i lam] t IH]; intros acc r H; simpl in H.
    - inversion H; subst. lia.
    - destruct (list_nthN cs i) as [c|] eqn:E; [|discriminate].
      apply IH in H. rewrite eval_laxpy in H.
      apply list_nthN_in in E. rewrite Forall_forall in Hcs. specialize (Hcs _ E).
      pose proof (Pos2Z.neg_is_neg lam). nia.
  Qed.

  Lemma comb_lin_ge cs : Forall (fun c => eval v c <= 0) cs ->
    forall lams acc r, comb_lin cs lams acc = Some r -> eval v acc <= eval v r.
  Proof.
    intros Hcs lams. induction lams as [|[lam c] t IH]; intros acc r H; simpl in H.
    - inversion H; subst. lia.
    - destruct (lin_mem c cs) eqn:E; [|discriminate].
      apply IH in H. rewrite eval_laxpy in H.
      apply lin_mem_sound in E. rewrite Forall_forall in Hcs. specialize (Hcs _ E).
      pose proof (Pos2Z.neg_is_neg lam). nia.
  Qed.

  Lemma hint_residual_ge S h a r :
    sat v S -> hint_residual S h a = Some r -> Zpos (hint_k h) * eval v a <= eval v r.
  Proof.
    intros HS. unfold hint_residual. destruct h as [|k lams|k lams]; cbn [hint_k]; intros H.
    - inversion H; subst. lia.
    - apply (comb_idx_ge (scons S) (sat_cons v S HS)) in H. rewrite eval_lscale in H. lia.
    - apply (comb_lin_ge (scons S) (sat_cons v S HS)) in H. rewrite eval_lscale in H. lia.
  Qed.

  Theorem entails_nonpos_sound S h a :
    entails_nonpos S h a = true -> sat v S -> eval v a <= 0.
  Proof.
    unfold entails_nonpos. intros H HS.
    destruct (hint_residual S h a) as [r|] eqn:E; [|discriminate].
    pose proof (hint_residual_ge S h a r HS E) as Hge.
    pose proof (itv_hi_lt_sound _ _ _ H (sat_range v S r HS)) as Hlt.
    nia.
  Qed.
End Soundness.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition entails_ub (S : store) (h : hint) (a : lin) (b : Z) : bool :=
  entails_nonpos S h (laddc a (- b)).
(* [comment removed for export] *)
Definition entails_lb (S : store) (h : hint) (a : lin) (b : Z) : bool :=
  entails_nonpos S h (laddc (lneg a) b).
(* [comment removed for export] *)
Definition entails_ltc (S : store) (h : hint) (a : lin) (b : Z) : bool :=
  entails_nonpos S h (laddc a (1 - b)).
(* [comment removed for export] *)
Definition entails_gtc (S : store) (h : hint) (a : lin) (b : Z) : bool :=
  entails_nonpos S h (laddc (lneg a) (b + 1)).
(* [comment removed for export] *)
Definition entails_le2 (S : store) (h : hint) (a b : lin) : bool :=
  entails_nonpos S h (lsub a b).
(* [comment removed for export] *)
Definition entails_lt2 (S : store) (h : hint) (a b : lin) : bool :=
  entails_nonpos S h (laddc (lsub a b) 1).
(* [comment removed for export] *)
Definition entails_eq2 (S : store) (h1 h2 : hint) (a b : lin) : bool :=
  lin_eqb a b || (entails_le2 S h1 a b && entails_le2 S h2 b a).
(* [comment removed for export] *)
Definition entails_in_itv (S : store) (hlo hhi : hint) (a : lin) (i : itv) : bool :=
  (match fst i with None => true | Some lo => entails_lb S hlo a lo end)
  && (match snd i with None => true | Some hi => entails_ub S hhi a hi end).
(* [comment removed for export] *)
Definition is_unsat (S : store) (h : hint) : bool := entails_nonpos S h (lconst 1).

Section Derived.
  Variable v : val.
  Variable S : store.
  Hypothesis HS : sat v S.

  Lemma entails_ub_sound h a b : entails_ub S h a b = true -> eval v a <= b.
  Proof.
    intros H. apply (entails_nonpos_sound v) in H; auto. rewrite eval_laddc in H. lia.
  Qed.

  Lemma entails_lb_sound h a b : entails_lb S h a b = true -> b <= eval v a.
  Proof.
    intros H. apply (entails_nonpos_sound v) in H; auto. rewrite eval_laddc, eval_lneg in H. lia.
  Qed.

  Lemma entails_ltc_sound h a b : entails_ltc S h a b = true -> eval v a < b.
  Proof.
    intros H. apply (entails_nonpos_sound v) in H; auto. rewrite eval_laddc in H. lia.
  Qed.

  Lemma entails_gtc_sound h a b : entails_gtc S h a b = true -> b < eval v a.
  Proof.
    intros H. apply (entails_nonpos_sound v) in H; auto. rewrite eval_laddc, eval_lneg in H. lia.
  Qed.

  Lemma entails_le2_sound h a b : entails_le2 S h a b = true -> eval v a <= eval v b.
  Proof.
    intros H. apply (entails_nonpos_sound v) in H; auto. rewrite eval_lsub in H. lia.
  Qed.

  Lemma entails_lt2_sound h a b : entails_lt2 S h a b = true -> eval v a < eval v b.
  Proof.
    intros H. apply (entails_nonpos_sound v) in H; auto. rewrite eval_laddc, eval_lsub in H. lia.
  Qed.

  Lemma entails_eq2_sound h1 h2 a b : entails_eq2 S h1 h2 a b = true -> eval v a = eval v b.
  Proof.
    unfold entails_eq2. intros H. apply orb_prop in H as [H|H].
    - now apply lin_eqb_sound.
    - apply andb_prop in H as [H1 H2].
      apply entails_le2_sound in H1. apply entails_le2_sound in H2. lia.
  Qed.

  Lemma entails_in_itv_sound hlo hhi a i :
    entails_in_itv S hlo hhi a i = true -> in_itv (eval v a) i.
  Proof.
    unfold entails_in_itv. intros H. apply andb_prop in H as [H1 H2].
    destruct i as [[lo|] [hi|]]; simpl in *; split; simpl;
      first [ eapply entails_lb_sound; eassumption
            | eapply entails_ub_sound; eassumption
            | exact I ].
  Qed.
End Derived.

Lemma is_unsat_sound S h v : is_unsat S h = true -> ~ sat v S.
Proof.
  intros H HS. pose proof (entails_nonpos_sound v S h _ H HS) as H'.
  rewrite eval_lconst in H'. lia.
Qed.

(* [comment removed for export] *)
Definition entails_nonpos_with (S : store) (mk : store -> lin -> hint) (a : lin) : bool :=
  entails_nonpos S HBox a || entails_nonpos S (mk S a) a.

Lemma entails_nonpos_with_sound S mk a v :
  entails_nonpos_with S mk a = true -> sat v S -> eval v a <= 0.
Proof.
  unfold entails_nonpos_with. intros H HS.
  apply orb_prop in H as [H|H]; eapply entails_nonpos_sound; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition hint_ub (S : store) (h : hint) (a : lin) : option Z :=
  match hint_residual S h a with
  | None => None
  | Some r =>
      match itv_hi (lin_range (sbox S) r) with
      | Some U => Some (zdivf U (Zpos (hint_k h)))   (* [comment removed for export] *)
      | None => None
      end
  end.

Lemma hint_ub_sound S h a b v : hint_ub S h a = Some b -> sat v S -> eval v a <= b.
Proof.
  unfold hint_ub. intros H HS.
  destruct (hint_residual S h a) as [r|] eqn:E; [|discriminate].
  pose proof (hint_residual_ge v S h a r HS E) as Hge.
  pose proof (sat_range v S r HS) as Hr.
  destruct (lin_range (sbox S) r) as [rlo [U|]]; simpl in H; [|discriminate].
  inversion H; subst. destruct Hr as [_ HU]. simpl in HU. rewrite zdivf_eq.
  apply Z.div_le_lower_bound; lia.
Qed.

(* [comment removed for export] *)
Definition hint_lb (S : store) (h : hint) (a : lin) : option Z :=
  match hint_ub S h (lneg a) with Some u => Some (- u) | None => None end.

Lemma hint_lb_sound S h a b v : hint_lb S h a = Some b -> sat v S -> b <= eval v a.
Proof.
  unfold hint_lb. intros H HS.
  destruct (hint_ub S h (lneg a)) as [u|] eqn:E; [|discriminate]. inversion H; subst.
  pose proof (hint_ub_sound S h (lneg a) u v E HS) as Hu. rewrite eval_lneg in Hu. lia.
Qed.
