(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnModel BnTree BnInv BnBridge BgState BgInv BgLib BgTree.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU2 Require Import W_ctxfree3.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgRepU Require Import BgRepDefs BgRep BgLayer BgPlace.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation ops := (tree_ops bptr).
Local Notation ST := (bstate bptr).

Fixpoint tfrees {A} (ps : list bptr) (k : btree bptr A) : btree bptr A :=
  match ps with [] => k | p :: ps' => TFree p (tfrees ps' k) end.

Lemma embed_tfrees : forall {A} ps (k : btree bptr A), embed (tfrees ps k) = lfrees ps (embed k).
Proof. intros A ps k. induction ps as [|p ps IH]; cbn [tfrees lfrees embed]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma tfrees_app : forall {A} l1 l2 (k : btree bptr A), tfrees (l1 ++ l2) k = tfrees l1 (tfrees l2 k).
Proof. intros A l1 l2 k. induction l1 as [|p l1 IH]; cbn [app tfrees]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Definition pinv (s s' : ST) : Prop :=
  st_ctx s' = st_ctx s /\ st_ri s' = st_ri s /\ st_n0 s' = st_n0 s /\ st_rbits s' = st_rbits s /\ st_rshift s' = st_rshift s
  /\ firstn NFIX (st_bns s') = firstn NFIX (st_bns s) /\ length (st_bns s') = length (st_bns s).

Lemma pinv_refl : forall s, pinv s s.
Proof. intros s. unfold pinv. auto 10. Qed.

Lemma pinv_trans : forall s1 s2 s3, pinv s1 s2 -> pinv s2 s3 -> pinv s1 s3.
Proof. intros s1 s2 s3 (A1 & A2 & A3 & A4 & A5 & A6 & A7) (B1 & B2 & B3 & B4 & B5 & B6 & B7). unfold pinv. repeat split; congruence. Qed.

Lemma firstn_list_set_above : forall {A} (l : list A) n i x, (n <= i)%nat -> firstn n (list_set l i x) = firstn n l.
Proof.
  intros A l. induction l as [|y l IH]; intros n i x H; destruct i as [|i]; destruct n as [|n]; cbn [list_set firstn]; try reflexivity; try lia.
  f_equal. apply IH. lia.
Qed.

Lemma pinv_setbn_pool : forall (s : ST) j b, pinv s (setbn (RPool j) b s).
Proof.
  intros s j b. unfold pinv, setbn, set_bns. cbn [st_bns st_ctx st_ri st_n0 st_rbits st_rshift]. repeat split.
  - apply firstn_list_set_above. unfold RPool. lia.
  - apply list_set_length.
Qed.

Definition pool_vals (s : ST) (i cnt : nat) : list (bignum bptr) := map (fun j => getbn (RPool j) s) (seq i cnt).

Lemma pfv_tree : forall cnt i (s : ST),
  (forall j, (i <= j < i + cnt)%nat -> bn_flags (getbn (RPool j) s) = 0) ->
  exists s', (forall B (K : unit * ST -> btree bptr B), tbind (pool_free_vals ops i cnt s) K = tfrees (val_ids (pool_vals s i cnt)) (K (tt, s')))
             /\ pinv s s' /\ (forall j, (i + cnt <= j)%nat -> getbn (RPool j) s' = getbn (RPool j) s)
             /\ skipn (NFIX + (i + cnt)) (st_bns s') = skipn (NFIX + (i + cnt)) (st_bns s).
Proof.
  induction cnt as [|n IH]; intros i s HF.
  - exists s. split; [intros B K; reflexivity|]. split; [apply pinv_refl|]. split; [auto| reflexivity].
  - set (b := getbn (RPool i) s).
    assert (FL : bn_flags b = 0) by (apply HF; lia).
    destruct (bn_d b) as [p|] eqn:Ed.
    + set (s1 := setbn (RPool i) (bn_nil 0) s).
      assert (G1 : forall j, j <> i -> getbn (RPool j) s1 = getbn (RPool j) s).
      { intros j Hj. unfold s1. apply getbn_setbn_other. unfold RPool. lia. }
      destruct (IH (S i) s1) as (s' & ET & PI & GO & SK).
      { intros j Hj. rewrite G1 by lia. apply HF. lia. }
      exists s'. split; [|split; [|split]].
      * intros B K. cbn [pool_free_vals]. unfold pool_vals. cbn [seq map]. rewrite val_ids_cons.
        unfold bbind at 1 2. unfold bget at 1. cbn [bind ret tree_ops tbind fst snd]. fold b.
        unfold BN_clear_free, bbind, bget, bset, bret, bfree_opt, bfree, bunr, has_flag. cbn [bind ret unreachable lib_free tree_ops tbind fst snd].
        fold b. rewrite Ed. cbv beta. fold b. rewrite FL, Ed. unfold BN_FLG_STATIC_DATA, BN_FLG_MALLOCED.
        change (negb (Z.land 0 2 =? 0)) with false. change (negb (Z.land 0 1 =? 0)) with false. cbn [tbind fst snd W_ctxfree3.opt_ids app].
        fold s1. cbn [tfrees]. f_equal. rewrite ET. f_equal. f_equal. unfold pool_vals. apply map_ext_in. intros j Hj. apply in_seq in Hj. apply G1. lia.
      * eapply pinv_trans; [apply pinv_setbn_pool| exact PI].
      * intros j Hj. rewrite GO by lia. apply G1. lia.
      * replace (NFIX + (i + S n))%nat with (NFIX + (S i + n))%nat by lia. rewrite SK. unfold s1. rewrite st_bns_setbn.
        apply skipn_list_set_below. unfold RPool. lia.
    + destruct (IH (S i) s) as (s' & ET & PI & GO & SK).
      { intros j Hj. apply HF. lia. }
      exists s'. split.
      { intros B K. cbn [pool_free_vals]. unfold pool_vals. cbn [seq map]. rewrite val_ids_cons.
        unfold bbind at 1 2. unfold bget at 1. cbn [bind ret tree_ops tbind fst snd]. fold b. rewrite Ed.
        unfold bret. cbn [ret tree_ops tbind fst snd W_ctxfree3.opt_ids app]. apply ET. }
      split; [exact PI|]. split; [intros j Hj; apply GO; lia|].
      replace (NFIX + (i + S n))%nat with (NFIX + (S i + n))%nat by lia. exact SK.
Qed.

Lemma skipn_nth_cons : forall {A} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  intros A l. induction l as [|x l IH]; intros k d H; [cbn in H; lia|]. destruct k as [|k]; [reflexivity|].
  cbn [skipn nth]. apply IH. cbn in H. lia.
Qed.

Lemma pool_vals_skipn : forall cnt (s : ST) i, (NFIX + i + cnt <= length (st_bns s))%nat ->
  pool_vals s i cnt = firstn cnt (skipn (NFIX + i) (st_bns s)).
Proof.
  induction cnt as [|n IH]; intros s i H; [reflexivity|]. unfold pool_vals in *. cbn [seq map].
  rewrite (skipn_nth_cons (st_bns s) (NFIX + i) (bn_nil 0)) by lia. cbn [firstn]. f_equal.
  rewrite IH by lia. replace (NFIX + S i)%nat with (S (NFIX + i)) by lia. reflexivity.
Qed.

Lemma tbind_tfrees : forall {A B} ps (t : btree bptr A) (K : A -> btree bptr B), tbind (tfrees ps t) K = tfrees ps (tbind t K).
Proof. intros A B ps t K. induction ps as [|p ps IH]; cbn [tfrees tbind]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma pfin_tree : forall items k (s : ST),
  (NFIX + BN_CTX_POOL_SIZE * (k + length items) <= length (st_bns s))%nat ->
  (forall j, (BN_CTX_POOL_SIZE * k <= j < BN_CTX_POOL_SIZE * (k + length items))%nat -> bn_flags (getbn (RPool j) s) = 0) ->
  exists s', (forall B (K : unit * ST -> btree bptr B),
                tbind (pool_finish ops items k s) K = tfrees (item_ids items (skipn (NFIX + BN_CTX_POOL_SIZE * k) (st_bns s))) (K (tt, s')))
             /\ pinv s s'.
Proof.
  induction items as [|it rest IH]; intros k s HL HF.
  - exists s. split; [intros B K; reflexivity| apply pinv_refl].
  - cbn [length] in HL, HF. unfold BN_CTX_POOL_SIZE in *.
    destruct (pfv_tree 16 (16 * k) s) as (s1 & E1 & P1 & G1 & S1); [intros j Hj; apply HF; lia|].
    pose proof P1 as (_ & _ & _ & _ & _ & _ & L1).
    destruct (IH (S k) s1) as (s' & E2 & P2).
    { rewrite L1. unfold BN_CTX_POOL_SIZE. lia. }
    { unfold BN_CTX_POOL_SIZE. intros j Hj. rewrite G1 by lia. apply HF. lia. }
    exists s'. split; [|eapply pinv_trans; eauto].
    intros B K. cbn [pool_finish]. unfold bbind at 1 2. cbn [bind tree_ops].
    rewrite (E1 _ (fun p => tbind (bfree ops it (snd p)) (fun p0 => pool_finish ops rest (S k) (snd p0)))).
    rewrite tbind_tfrees. unfold bfree. cbn [bind ret lib_free tree_ops tbind fst snd].
    rewrite (E2 _ K). rewrite item_ids_cons, tfrees_app. cbn [tfrees].
    rewrite (pool_vals_skipn 16 s (16 * k)) by lia.
    f_equal. f_equal. f_equal. f_equal.
    rewrite skipn_skipn. unfold BN_CTX_POOL_SIZE. replace (16 + (NFIX + 16 * k))%nat with (NFIX + (16 * k + 16))%nat by lia.
    rewrite <- S1. f_equal. lia.
Qed.

Theorem BN_CTX_free_tree : forall (qc : bptr) (bs : ST), st_wf bs -> pool_fl0 bs = true ->
  embed (BN_CTX_free ops qc bs)
  = lfrees (ctx_free_ids (gx_indexes (st_ctx bs)) (gx_items (st_ctx bs)) (skipn NFIX (st_bns bs)) qc) (LRet (tt, st_ctx_freed bs)).
Proof.
  intros qc bs WF PF. pose proof WF as (EL & _).
  assert (HF : forall j, (j < BN_CTX_POOL_SIZE * length (gx_items (st_ctx bs)))%nat -> bn_flags (getbn (RPool j) bs) = 0).
  { intros j Hj. unfold pool_fl0 in PF. rewrite forallb_forall in PF. apply Z.eqb_eq. apply PF.
    unfold getbn, RPool. rewrite <- nth_skipn. apply nth_In. rewrite length_skipn. lia. }
  destruct (pfin_tree (gx_items (st_ctx bs)) 0 bs) as (s' & E1 & (P1 & P2 & P3 & P4 & P5 & P6 & P7)).
  { cbn [Nat.add]. rewrite EL. lia. }
  { intros j Hj. apply HF. cbn [Nat.add] in Hj. lia. }
  unfold BN_CTX_free. unfold bbind at 1. unfold bgetctx at 1. cbn [bind ret tree_ops tbind fst snd].
  unfold bbind at 1. cbn [bind tree_ops]. unfold ctx_free_ids.
  change (LRet (tt, st_ctx_freed bs)) with (embed (TRet (tt, st_ctx_freed bs))). rewrite <- embed_tfrees. f_equal. rewrite !tfrees_app.
  assert (EF : forall (K : unit * ST -> btree bptr (unit * ST)),
            tbind (bfree_opt ops (gx_indexes (st_ctx bs)) bs) K = tfrees (W_ctxfree3.opt_ids (gx_indexes (st_ctx bs))) (K (tt, bs))).
  { intros K. destruct (gx_indexes (st_ctx bs)) as [qi|]; reflexivity. }
  rewrite EF. f_equal. cbn [fst snd].
  unfold bbind at 1. cbn [bind tree_ops]. rewrite E1. f_equal. replace (NFIX + BN_CTX_POOL_SIZE * 0)%nat with NFIX by (unfold BN_CTX_POOL_SIZE; lia).
  f_equal. unfold bbind, bfree, bgetst, bsetbns, bsetctx. cbn [bind ret lib_free tree_ops tbind fst snd tfrees].
  f_equal. f_equal. f_equal. unfold st_ctx_freed, set_ctx, set_bns. cbn [st_bns st_ctx st_ri st_n0 st_rbits st_rshift].
  rewrite P2, P3, P4, P5, P6. reflexivity.
Qed.

Lemma BN_CTX_free_g_tree : forall (qc : bptr) (bs : ST), st_wf bs ->
  embed (BN_CTX_free_g ops qc bs)
  = if pool_fl0 bs then lfrees (ctx_free_ids (gx_indexes (st_ctx bs)) (gx_items (st_ctx bs)) (skipn NFIX (st_bns bs)) qc) (LRet (tt, st_ctx_freed bs))
    else LUnr.
Proof.
  intros qc bs WF. unfold BN_CTX_free_g. destruct (pool_fl0 bs) eqn:PF; [apply BN_CTX_free_tree; assumption| reflexivity].
Qed.
