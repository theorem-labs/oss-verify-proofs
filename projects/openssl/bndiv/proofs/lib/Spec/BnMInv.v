(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Sorted.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnInv BnSpecs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section MInv.
Context {ptr : Type}.
Local Notation LS := (lstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).

Definition bn_okm (b : BN) : Prop :=
  limbs (bn_buf b) /\ (bn_top b <= bn_dmax b)%nat /\ Z.of_nat (bn_dmax b) <= BN_WORDS_MAX /\ (bn_flags b = 0 \/ bn_flags b = 1).

Definition pool_okm (vals : list BN) : Prop := vals = [] \/ (length vals = 16%nat /\ Forall bn_okm vals).

(* [comment removed for export] *)
Fixpoint nondecr (l : list nat) : Prop :=
  match l with
  | [] => True
  | x :: l' => match l' with [] => True | y :: _ => (x <= y)%nat end /\ nondecr l'
  end.

Definition ctx_okm (c : bn_ctx ptr) : Prop :=
  cx_pused c = cx_used c /\ ((cx_used c <= 16)%nat /\ (cx_used c <= cx_psize c)%nat) /\ cx_psize c = length (cx_vals c)
  /\ nondecr (cx_frames c ++ [cx_used c])
  /\ (length (cx_frames c) <= cx_ssize c)%nat
  /\ (cx_pused c <> 0%nat -> cx_current c = cx_head c)
  /\ cx_err_stack c = 0%nat.

Definition st_okm (s : LS) : Prop :=
  bn_okm (ls_b1 s) /\ bn_okm (ls_b2 s) /\ bn_okm (ls_b3 s) /\ bn_okm (ls_b4 s) /\ bn_okm (ls_b5 s)
  /\ pool_okm (cx_vals (ls_ctx s)) /\ ctx_okm (ls_ctx s).

Definition valid_refm (r : bnref) (s : LS) : Prop :=
  match r with RPool i => (i < length (cx_vals (ls_ctx s)))%nat | _ => True end.

Lemma bn_okm_nil : forall f, f = 0 \/ f = 1 -> bn_okm (bn_nil f : BN).
Proof.
  intros f Hf. unfold bn_okm, bn_nil, bn_dmax, BN_WORDS_MAX. cbn. split; [constructor|]. split; [lia|]. split; [lia|exact Hf].
Qed.

Lemma st_okm_init : st_okm (ls_init : LS).
Proof.
  unfold st_okm, ls_init. cbn [ls_b1 ls_b2 ls_b3 ls_b4 ls_b5 ls_ctx ctx_nil cx_vals].
  repeat split; try (apply bn_okm_nil; right; reflexivity); try (left; reflexivity); cbn; try lia; try tauto.
Qed.

(* [comment removed for export] *)
Lemma nth_list_set_same : forall {A} (l : list A) i a d, (i < length l)%nat -> nth i (list_set l i a) d = a.
Proof. induction l as [|x l IH]; intros i a d Hi; cbn in *; [lia|]. destruct i; [reflexivity|]. apply IH. lia. Qed.

Lemma list_set_length : forall {A} (l : list A) i a, length (list_set l i a) = length l.
Proof. induction l as [|x l IH]; intros i a; cbn; [reflexivity|]. destruct i; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma list_set_nth_id : forall {A} (l : list A) i d, list_set l i (nth i l d) = l.
Proof. induction l as [|x l IH]; intros i d; cbn; [reflexivity|]. destruct i; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma getbn_setbn_same_m : forall r b (s : LS), valid_refm r s -> getbn r (setbn r b s) = b.
Proof.
  intros r b s Hv. destruct r as [| | | | |i]; try reflexivity.
  cbn [getbn setbn set_ctx ls_ctx ctx_set_vals cx_vals]. apply nth_list_set_same. exact Hv.
Qed.

Lemma setbn_getbn_id_m : forall r (s : LS), setbn r (getbn r s) s = s.
Proof.
  intros r s. destruct s as [b1 b2 b3 b4 b5 c]. destruct r as [| | | | |i]; try reflexivity.
  cbn [getbn setbn set_ctx ls_ctx ctx_set_vals cx_vals ls_b1 ls_b2 ls_b3 ls_b4 ls_b5]. rewrite list_set_nth_id.
  destruct c. reflexivity.
Qed.

Lemma valid_refm_setbn : forall r r' b (s : LS), valid_refm r' s -> valid_refm r' (setbn r b s).
Proof.
  intros r r' b s H. destruct r' as [| | | | |j]; try exact I. destruct r as [| | | | |i]; try exact H.
  cbn [valid_refm setbn set_ctx ls_ctx ctx_set_vals cx_vals] in *. rewrite list_set_length. exact H.
Qed.

Lemma Forall_list_set : forall {A} (P : A -> Prop) (l : list A) i a, Forall P l -> P a -> Forall P (list_set l i a).
Proof.
  induction l as [|x l IH]; intros i a Hl Ha; cbn; [constructor|]. inversion Hl; subst.
  destruct i; constructor; auto.
Qed.

Lemma st_okm_getbn : forall r (s : LS), st_okm s -> valid_refm r s -> bn_okm (getbn r s).
Proof.
  intros r s (H1 & H2 & H3 & H4 & H5 & Hp & _) Hv. destruct r as [| | | | |i]; try assumption.
  cbn [getbn valid_refm] in *. destruct Hp as [E|[_ Hf]]; [rewrite E in Hv; cbn in Hv; lia|].
  rewrite Forall_forall in Hf. apply Hf. apply nth_In. exact Hv.
Qed.

Lemma st_okm_setbn : forall r b (s : LS), st_okm s -> valid_refm r s -> bn_okm b -> st_okm (setbn r b s).
Proof.
  intros r b s Hs Hv Hb. pose proof Hs as (H1 & H2 & H3 & H4 & H5 & Hp & Hc).
  destruct r as [| | | | |i]; try (unfold st_okm; cbn [setbn ls_b1 ls_b2 ls_b3 ls_b4 ls_b5 ls_ctx]; tauto).
  unfold st_okm. cbn [setbn set_ctx ls_b1 ls_b2 ls_b3 ls_b4 ls_b5 ls_ctx ctx_set_vals cx_vals].
  repeat (split; [assumption|]). split.
  - destruct Hp as [E|[Hl Hf]]; [cbn [valid_refm] in Hv; rewrite E in Hv; cbn in Hv; lia|].
    right. split; [rewrite list_set_length; exact Hl| apply Forall_list_set; assumption].
  - unfold ctx_okm, ctx_set_vals in *. cbn [cx_pused cx_used cx_psize cx_vals cx_frames cx_ssize cx_current cx_head]. rewrite list_set_length. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma concat_map_list_set : forall (l : list BN) i, (i < length l)%nat ->
  exists L1 L2, concat (map bn_blocks l) = L1 ++ bn_blocks (nth i l (bn_nil 0)) ++ L2
                /\ forall b', concat (map bn_blocks (list_set l i b')) = L1 ++ bn_blocks b' ++ L2.
Proof.
  induction l as [|x l IH]; intros i Hi; cbn in Hi; [lia|]. destruct i as [|i].
  - exists [], (concat (map bn_blocks l)). split; [reflexivity|]. intros b'. reflexivity.
  - destruct (IH i ltac:(lia)) as (L1 & L2 & E1 & E2). exists (bn_blocks x ++ L1), L2. split.
    + cbn [map concat nth]. rewrite E1, <- app_assoc. reflexivity.
    + intros b'. cbn [list_set map concat]. rewrite E2, <- app_assoc. reflexivity.
Qed.

Lemma blocks_setbn_m : forall r (s : LS), valid_refm r s ->
  exists R, Permutation (blocks_of s) (bn_blocks (getbn r s) ++ R) /\
            forall b, Permutation (blocks_of (setbn r b s)) (bn_blocks b ++ R).
Proof.
  intros r s Hv. destruct s as [b1 b2 b3 b4 b5 c].
  set (T := opt_block (cx_head c) POOL_ITEM_BYTES ++ opt_block (cx_indexes c) (4 * Z.of_nat BN_CTX_START_FRAMES)).
  destruct r as [| | | | |i]; unfold blocks_of; cbn [getbn setbn ls_b1 ls_b2 ls_b3 ls_b4 ls_b5 ls_ctx]; fold T.
  - exists ([] ++ bn_blocks b2 ++ bn_blocks b3 ++ bn_blocks b4 ++ bn_blocks b5 ++ concat (map bn_blocks (cx_vals c)) ++ T).
    split; [|intros b]; apply perm_pick; reflexivity.
  - exists (bn_blocks b1 ++ bn_blocks b3 ++ bn_blocks b4 ++ bn_blocks b5 ++ concat (map bn_blocks (cx_vals c)) ++ T).
    split; [|intros b]; apply perm_pick; reflexivity.
  - exists ((bn_blocks b1 ++ bn_blocks b2) ++ bn_blocks b4 ++ bn_blocks b5 ++ concat (map bn_blocks (cx_vals c)) ++ T).
    split; [|intros b]; apply perm_pick; rewrite <- !app_assoc; reflexivity.
  - exists ((bn_blocks b1 ++ bn_blocks b2 ++ bn_blocks b3) ++ bn_blocks b5 ++ concat (map bn_blocks (cx_vals c)) ++ T).
    split; [|intros b]; apply perm_pick; rewrite <- !app_assoc; reflexivity.
  - exists ((bn_blocks b1 ++ bn_blocks b2 ++ bn_blocks b3 ++ bn_blocks b4) ++ concat (map bn_blocks (cx_vals c)) ++ T).
    split; [|intros b]; apply perm_pick; rewrite <- !app_assoc; reflexivity.
  - cbn [valid_refm ls_ctx] in Hv. destruct (concat_map_list_set (cx_vals c) i Hv) as (L1 & L2 & E1 & E2).
    destruct c as [hd cur vals pu ps idx fr ss us es tm]. cbn [ls_ctx cx_vals cx_head cx_indexes set_ctx ctx_set_vals] in *.
    exists ((bn_blocks b1 ++ bn_blocks b2 ++ bn_blocks b3 ++ bn_blocks b4 ++ bn_blocks b5 ++ L1) ++ L2 ++ T). split.
    + rewrite E1. apply perm_pick. rewrite <- !app_assoc. reflexivity.
    + intros b. rewrite E2. apply perm_pick. rewrite <- !app_assoc. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma In_concat_map_nth : forall (l : list BN) i p, (i < length l)%nat -> bn_d (nth i l (bn_nil 0)) = Some p ->
  In (p, 8 * Z.of_nat (bn_dmax (nth i l (bn_nil 0)))) (concat (map bn_blocks l)).
Proof.
  induction l as [|x l IH]; intros i p Hi Hd; cbn in Hi; [lia|]. cbn [map concat]. apply in_or_app. destruct i as [|i].
  - left. cbn [nth] in *. unfold bn_blocks. rewrite Hd. left. reflexivity.
  - right. cbn [nth] in *. apply IH; [lia| exact Hd].
Qed.

Lemma blocks_of_In_bn : forall r (s : LS) p, valid_refm r s -> bn_d (getbn r s) = Some p ->
  In (p, 8 * Z.of_nat (bn_dmax (getbn r s))) (blocks_of s).
Proof.
  intros r s p Hv Hd. unfold blocks_of.
  assert (HB : forall b : BN, bn_d b = Some p -> In (p, 8 * Z.of_nat (bn_dmax b)) (bn_blocks b))
    by (intros b Hb; unfold bn_blocks; rewrite Hb; left; reflexivity).
  destruct r as [| | | | |i]; cbn [getbn] in *.
  - apply in_or_app. left. apply HB. exact Hd.
  - apply in_or_app. right. apply in_or_app. left. apply HB. exact Hd.
  - do 2 (apply in_or_app; right). apply in_or_app. left. apply HB. exact Hd.
  - do 3 (apply in_or_app; right). apply in_or_app. left. apply HB. exact Hd.
  - do 4 (apply in_or_app; right). apply in_or_app. left. apply HB. exact Hd.
  - do 5 (apply in_or_app; right). apply in_or_app. left. apply In_concat_map_nth; assumption.
Qed.

Lemma blocks_of_In_head : forall (s : LS) h, cx_head (ls_ctx s) = Some h -> In (h, POOL_ITEM_BYTES) (blocks_of s).
Proof.
  intros s h Hh. unfold blocks_of. do 6 (apply in_or_app; right). apply in_or_app. left. rewrite Hh. left. reflexivity.
Qed.

Lemma blocks_of_In_idx : forall (s : LS) q, cx_indexes (ls_ctx s) = Some q ->
  In (q, 4 * Z.of_nat BN_CTX_START_FRAMES) (blocks_of s).
Proof.
  intros s q Hq. unfold blocks_of. do 7 (apply in_or_app; right). rewrite Hq. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ids_without : forall r (s : LS) p, NoDup (map fst (blocks_of s)) -> valid_refm r s -> bn_d (getbn r s) = Some p ->
  ~ In p (map fst (blocks_of (setbn r (bn_nil 0) s))).
Proof.
  intros r s p ND Hv Hd. destruct (blocks_setbn_m r s Hv) as (R & H1 & H2).
  specialize (H2 (bn_nil 0)). rewrite bn_blocks_nil in H2. cbn [app] in H2.
  unfold bn_blocks in H1. rewrite Hd in H1. cbn [app] in H1.
  apply (Permutation_map fst) in H1. apply (Permutation_map fst) in H2. cbn [map fst] in H1.
  apply (Permutation_NoDup H1) in ND. apply NoDup_cons_iff in ND. destruct ND as [Hn _].
  intros Hin. apply Hn. eapply Permutation_in; [exact H2| exact Hin].
Qed.

Lemma ids_bn_neq : forall r r' (s : LS) p p', NoDup (map fst (blocks_of s)) -> valid_refm r s -> valid_refm r' s -> r <> r' ->
  bn_d (getbn r s) = Some p -> bn_d (getbn r' s) = Some p' -> p <> p'.
Proof.
  intros r r' s p p' ND Hv Hv' Hne Hd Hd' E. subst p'. apply (ids_without r s p ND Hv Hd).
  pose proof (blocks_of_In_bn r' (setbn r (bn_nil 0) s) p) as H. rewrite getbn_setbn_other in H by exact Hne.
  specialize (H (valid_refm_setbn _ _ _ _ Hv') Hd'). apply (in_map fst) in H. exact H.
Qed.

Lemma ids_bn_head_neq : forall r (s : LS) p h, NoDup (map fst (blocks_of s)) -> valid_refm r s ->
  bn_d (getbn r s) = Some p -> cx_head (ls_ctx s) = Some h -> p <> h.
Proof.
  intros r s p h ND Hv Hd Hh E. subst h. apply (ids_without r s p ND Hv Hd).
  pose proof (blocks_of_In_head (setbn r (bn_nil 0) s) p) as H.
  destruct (ctx_same_setbn r (bn_nil 0) s) as (A1 & _). rewrite <- A1 in Hh. specialize (H Hh). apply (in_map fst) in H. exact H.
Qed.

Lemma ids_bn_idx_neq : forall r (s : LS) p q, NoDup (map fst (blocks_of s)) -> valid_refm r s ->
  bn_d (getbn r s) = Some p -> cx_indexes (ls_ctx s) = Some q -> p <> q.
Proof.
  intros r s p q ND Hv Hd Hq E. subst q. apply (ids_without r s p ND Hv Hd).
  pose proof (blocks_of_In_idx (setbn r (bn_nil 0) s) p) as H.
  destruct (ctx_same_setbn r (bn_nil 0) s) as (_ & _ & _ & _ & A5 & _). rewrite <- A5 in Hq. specialize (H Hq). apply (in_map fst) in H. exact H.
Qed.

Lemma ids_head_idx_neq : forall (s : LS) h q, NoDup (map fst (blocks_of s)) ->
  cx_head (ls_ctx s) = Some h -> cx_indexes (ls_ctx s) = Some q -> h <> q.
Proof.
  intros s h q ND Hh Hq E. subst q. unfold blocks_of in ND. rewrite Hh, Hq in ND. cbn [opt_block] in ND.
  rewrite !map_app in ND. do 6 (apply NoDup_app_remove_l in ND). cbn in ND.
  apply NoDup_cons_iff in ND. destruct ND as [Hn _]. apply Hn. left. reflexivity.
Qed.


Lemma nondecr_app_inv : forall (l1 l2 : list nat), nondecr (l1 ++ l2) -> nondecr l1 /\ nondecr l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2 H; [split; [exact I| exact H]|].
  cbn [app nondecr] in *. destruct H as [Hx H]. destruct (IH l2 H) as [H1 H2]. split; [|exact H2]. split; [|exact H1].
  destruct l1 as [|y l1]; [exact I|]. exact Hx.
Qed.

Lemma nondecr_snoc : forall (l : list nat) x y, nondecr (l ++ [x]) -> (x <= y)%nat -> nondecr (l ++ [x; y]).
Proof.
  induction l as [|z l IH]; intros x y H Hxy; cbn [app nondecr] in *; [tauto|].
  destruct H as [Hz H]. split; [|apply IH; assumption]. destruct l as [|w l]; cbn [app] in *; exact Hz.
Qed.

Lemma nondecr_last_le : forall (l : list nat) x y, nondecr (l ++ [x; y]) -> (x <= y)%nat.
Proof.
  induction l as [|z l IH]; intros x y H; cbn [app nondecr] in *; [tauto|]. apply IH. tauto.
Qed.

Lemma nondecr_drop_last : forall (l : list nat) x y, nondecr (l ++ [x; y]) -> nondecr (l ++ [x]).
Proof.
  induction l as [|z l IH]; intros x y H; cbn [app nondecr] in *; [tauto|].
  destruct H as [Hz H]. split; [|apply IH with y; exact H]. destruct l as [|w l]; cbn [app] in *; exact Hz.
Qed.

End MInv.

Lemma bnref_eq_dec : forall r r' : bnref, {r = r'} + {r <> r'}.
Proof. decide equality. apply Nat.eq_dec. Qed.

Lemma in_dec_bnref : forall (r : bnref) (l : list bnref), {In r l} + {~ In r l}.
Proof. intros. apply in_dec. apply bnref_eq_dec. Qed.

