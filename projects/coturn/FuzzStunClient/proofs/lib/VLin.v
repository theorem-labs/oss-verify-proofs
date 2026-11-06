(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VMap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition sym := positive.
Definition val := sym -> Z.
Definition term := (sym * Z)%type.

Record lin := mkLin { lc : Z ; lt : list term }.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint eval_terms (v : val) (l : list term) : Z :=
  match l with
  | [] => 0
  | (s, k) :: t => k * v s + eval_terms v t
  end.

Definition eval (v : val) (a : lin) : Z := lc a + eval_terms v (lt a).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lconst (c : Z) : lin := mkLin c [].
Definition lzero : lin := lconst 0.
Definition lsym (s : sym) : lin := mkLin 0 [(s, 1)].
Definition lsymc (s : sym) (c : Z) : lin := mkLin c [(s, 1)].
Definition lterm (k : Z) (s : sym) : lin :=
  if Z.eqb k 0 then lzero else mkLin 0 [(s, k)].

Definition lin_is_const (a : lin) : bool :=
  match lt a with [] => true | _ => false end.

(* [comment removed for export] *)
Definition lin_single (a : lin) : option (sym * Z) :=
  match lt a with
  | [sk] => Some sk
  | _ => None
  end.

Fixpoint terms_coef (l : list term) (s : sym) : Z :=
  match l with
  | [] => 0
  | (s', k) :: t => if Pos.eqb s s' then k else terms_coef t s
  end.

(* [comment removed for export] *)
Definition lcoef (a : lin) (s : sym) : Z := terms_coef (lt a) s.

Definition lsyms (a : lin) : list sym := map fst (lt a).

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint terms_scale (k : Z) (l : list term) : list term :=
  match l with
  | [] => []
  | (s, c) :: t => (s, k * c) :: terms_scale k t
  end.

Definition lscale (k : Z) (a : lin) : lin :=
  if Z.eqb k 0 then lzero
  else if Z.eqb k 1 then a
  else mkLin (k * lc a) (terms_scale k (lt a)).

Definition lneg (a : lin) : lin := mkLin (- lc a) (terms_scale (-1) (lt a)).

Definition laddc (a : lin) (c : Z) : lin := mkLin (lc a + c) (lt a).

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint terms_axpy (k : Z) (l1 : list term) {struct l1} : list term -> list term :=
  match l1 with
  | [] => fun l2 => terms_scale k l2
  | (s1, c1) :: t1 =>
      fix aux (l2 : list term) {struct l2} : list term :=
        match l2 with
        | [] => l1
        | (s2, c2) :: t2 =>
            match Pos.compare s1 s2 with
            | Lt => (s1, c1) :: terms_axpy k t1 l2
            | Gt => (s2, k * c2) :: aux t2
            | Eq => let c := c1 + k * c2 in
                    if Z.eqb c 0 then terms_axpy k t1 t2
                    else (s1, c) :: terms_axpy k t1 t2
            end
        end
  end.

(* [comment removed for export] *)
Definition laxpy (a : lin) (k : Z) (b : lin) : lin :=
  if Z.eqb k 0 then a
  else mkLin (lc a + k * lc b) (terms_axpy k (lt a) (lt b)).

Definition ladd (a b : lin) : lin := mkLin (lc a + lc b) (terms_axpy 1 (lt a) (lt b)).
Definition lsub (a b : lin) : lin := mkLin (lc a - lc b) (terms_axpy (-1) (lt a) (lt b)).

(* [comment removed for export] *)
Definition lnorm (c : Z) (l : list term) : lin :=
  fold_left (fun acc sk => ladd acc (lterm (snd sk) (fst sk))) l (lconst c).

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint terms_eqb (l1 l2 : list term) : bool :=
  match l1, l2 with
  | [], [] => true
  | (s1, c1) :: t1, (s2, c2) :: t2 => Pos.eqb s1 s2 && Z.eqb c1 c2 && terms_eqb t1 t2
  | _, _ => false
  end.

Definition lin_eqb (a b : lin) : bool := Z.eqb (lc a) (lc b) && terms_eqb (lt a) (lt b).

(* [comment removed for export] *)
Fixpoint terms_wf_from (p : sym) (l : list term) : bool :=
  match l with
  | [] => true
  | (s, c) :: t => Pos.ltb p s && negb (Z.eqb c 0) && terms_wf_from s t
  end.

Definition lin_wf (a : lin) : bool :=
  match lt a with
  | [] => true
  | (s, c) :: t => negb (Z.eqb c 0) && terms_wf_from s t
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint terms_subst (sigma : pmap lin) (l : list term) (acc : lin) : lin :=
  match l with
  | [] => acc
  | (s, k) :: t =>
      let e := match pm_get s sigma with Some e => e | None => lsym s end in
      terms_subst sigma t (laxpy acc k e)
  end.

Definition lsubst (sigma : pmap lin) (a : lin) : lin :=
  terms_subst sigma (lt a) (lconst (lc a)).

Definition vsubst (v : val) (sigma : pmap lin) : val :=
  fun s => match pm_get s sigma with Some e => eval v e | None => v s end.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma eval_lconst v c : eval v (lconst c) = c.
Proof. unfold eval; cbn -[Z.mul Z.add Z.sub Z.opp]. lia. Qed.

Lemma eval_lzero v : eval v lzero = 0.
Proof. reflexivity. Qed.

Lemma eval_lsym v s : eval v (lsym s) = v s.
Proof. unfold eval; cbn -[Z.mul Z.add Z.sub Z.opp]. lia. Qed.

Lemma eval_lsymc v s c : eval v (lsymc s c) = v s + c.
Proof. unfold eval; cbn -[Z.mul Z.add Z.sub Z.opp]. lia. Qed.

Lemma eval_lterm v k s : eval v (lterm k s) = k * v s.
Proof.
  unfold lterm. destruct (Z.eqb_spec k 0).
  - subst. rewrite eval_lzero. lia.
  - unfold eval; cbn -[Z.mul Z.add Z.sub Z.opp]. lia.
Qed.

Lemma eval_terms_scale v k l : eval_terms v (terms_scale k l) = k * eval_terms v l.
Proof.
  induction l as [|[s c] t IH]; simpl; [lia|]. rewrite IH. lia.
Qed.

Lemma eval_lscale v k a : eval v (lscale k a) = k * eval v a.
Proof.
  unfold lscale. destruct (Z.eqb_spec k 0).
  - subst. rewrite eval_lzero. lia.
  - destruct (Z.eqb_spec k 1).
    + subst. lia.
    + unfold eval; cbn -[Z.mul Z.add Z.sub Z.opp]. rewrite eval_terms_scale. lia.
Qed.

Lemma eval_lneg v a : eval v (lneg a) = - eval v a.
Proof. unfold eval, lneg; cbn -[Z.mul Z.add Z.sub Z.opp]. rewrite eval_terms_scale. lia. Qed.

Lemma eval_laddc v a c : eval v (laddc a c) = eval v a + c.
Proof. unfold eval, laddc; cbn -[Z.mul Z.add Z.sub Z.opp]. lia. Qed.

Lemma eval_terms_axpy v k l1 : forall l2,
  eval_terms v (terms_axpy k l1 l2) = eval_terms v l1 + k * eval_terms v l2.
Proof.
  induction l1 as [|[s1 c1] t1 IH1]; intros l2.
  - simpl. rewrite eval_terms_scale. lia.
  - induction l2 as [|[s2 c2] t2 IH2].
    + simpl. lia.
    + simpl. destruct (Pos.compare_spec s1 s2).
      * subst. destruct (Z.eqb_spec (c1 + k * c2) 0).
        -- rewrite IH1. simpl. lia.
        -- simpl. rewrite IH1. simpl. lia.
      * simpl. rewrite IH1. simpl. lia.
      * simpl. simpl in IH2. rewrite IH2. lia.
Qed.

Lemma eval_laxpy v a k b : eval v (laxpy a k b) = eval v a + k * eval v b.
Proof.
  unfold laxpy. destruct (Z.eqb_spec k 0).
  - subst; lia.
  - unfold eval; cbn -[Z.mul Z.add Z.sub Z.opp]. rewrite eval_terms_axpy. lia.
Qed.

Lemma eval_ladd v a b : eval v (ladd a b) = eval v a + eval v b.
Proof. unfold eval, ladd; cbn -[Z.mul Z.add Z.sub Z.opp]. rewrite eval_terms_axpy. lia. Qed.

Lemma eval_lsub v a b : eval v (lsub a b) = eval v a - eval v b.
Proof. unfold eval, lsub; cbn -[Z.mul Z.add Z.sub Z.opp]. rewrite eval_terms_axpy. lia. Qed.

Lemma eval_lnorm v c l : eval v (lnorm c l) = c + eval_terms v l.
Proof.
  unfold lnorm.
  assert (H : forall acc, eval v (fold_left (fun acc sk => ladd acc (lterm (snd sk) (fst sk))) l acc)
                         = eval v acc + eval_terms v l).
  { induction l as [|[s k] t IH]; intros acc; simpl.
    - lia.
    - rewrite IH, eval_ladd, eval_lterm. lia. }
  rewrite H, eval_lconst. reflexivity.
Qed.

Lemma eval_single v a s k : lin_single a = Some (s, k) -> eval v a = lc a + k * v s.
Proof.
  unfold lin_single, eval. destruct (lt a) as [|[s' k'] [|x t]]; try discriminate.
  intros H; inversion H; subst. simpl. lia.
Qed.

Lemma eval_is_const v a : lin_is_const a = true -> eval v a = lc a.
Proof.
  unfold lin_is_const, eval. destruct (lt a); [simpl; lia|discriminate].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma terms_eqb_sound l1 : forall l2, terms_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|[s1 c1] t1 IH]; intros [|[s2 c2] t2] H; simpl in H; try discriminate; auto.
  apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [H1 H2].
  apply Pos.eqb_eq in H1. apply Z.eqb_eq in H2. subst. f_equal. auto.
Qed.

Lemma lin_eqb_eq a b : lin_eqb a b = true -> a = b.
Proof.
  unfold lin_eqb. intros H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply terms_eqb_sound in H2.
  destruct a, b; simpl in *; congruence.
Qed.

Lemma lin_eqb_sound v a b : lin_eqb a b = true -> eval v a = eval v b.
Proof. intros H. apply lin_eqb_eq in H. now subst. Qed.

Lemma terms_eqb_refl l : terms_eqb l l = true.
Proof.
  induction l as [|[s c] t IH]; simpl; auto.
  rewrite Pos.eqb_refl, Z.eqb_refl. simpl. exact IH.
Qed.

Lemma lin_eqb_refl a : lin_eqb a a = true.
Proof. unfold lin_eqb. rewrite Z.eqb_refl, terms_eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma eval_terms_subst v sigma l : forall acc,
  eval v (terms_subst sigma l acc) = eval v acc + eval_terms (vsubst v sigma) l.
Proof.
  induction l as [|[s k] t IH]; intros acc; simpl.
  - lia.
  - rewrite IH, eval_laxpy. unfold vsubst at 2.
    destruct (pm_get s sigma); [lia|]. rewrite eval_lsym. lia.
Qed.

Lemma eval_lsubst v sigma a : eval v (lsubst sigma a) = eval (vsubst v sigma) a.
Proof.
  unfold lsubst. rewrite eval_terms_subst, eval_lconst. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma eval_terms_ext v1 v2 l :
  (forall s, In s (map fst l) -> v1 s = v2 s) -> eval_terms v1 l = eval_terms v2 l.
Proof.
  induction l as [|[s k] t IH]; intros H; simpl; auto.
  rewrite (H s) by (simpl; auto). rewrite IH; auto. intros; apply H; simpl; auto.
Qed.

Lemma eval_ext v1 v2 a :
  (forall s, In s (lsyms a) -> v1 s = v2 s) -> eval v1 a = eval v2 a.
Proof. intros H. unfold eval. rewrite (eval_terms_ext v1 v2); auto. Qed.

Lemma eval_ext_all v1 v2 a : (forall s, v1 s = v2 s) -> eval v1 a = eval v2 a.
Proof. intros; apply eval_ext; auto. Qed.

(* [comment removed for export] *)
Lemma eval_lsubst_agree v v' sigma a :
  (forall s, In s (lsyms a) -> v' s = vsubst v sigma s) ->
  eval v' a = eval v (lsubst sigma a).
Proof.
  intros H. rewrite eval_lsubst. apply eval_ext. exact H.
Qed.

(* [comment removed for export] *)
Lemma terms_coef_notin l s : ~ In s (map fst l) -> terms_coef l s = 0.
Proof.
  induction l as [|[s' k] t IH]; simpl; intros H; auto.
  destruct (Pos.eqb_spec s s'); [subst; tauto|]. apply IH. tauto.
Qed.
