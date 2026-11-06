(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnInv BgState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition BG_BSZ : Z := 4096.
Definition BG_NBLK : nat := 72.
Definition BG_DMAX : Z := 512.
Definition BG_POOL : nat := 48.
Definition BG_NF : nat := 7.
Definition BG_DEPTH : nat := 32.

Lemma list_set_length : forall {A} (l : list A) i a, length (list_set l i a) = length l.
Proof. induction l as [|x l IH]; intros i a; cbn; [reflexivity|]. destruct i; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma nth_list_set_same : forall {A} (l : list A) i a d, (i < length l)%nat -> nth i (list_set l i a) d = a.
Proof. induction l as [|x l IH]; intros i a d Hi; cbn in *; [lia|]. destruct i; [reflexivity|]. apply IH. lia. Qed.

Lemma nth_list_set_other : forall {A} (l : list A) i j a d, i <> j -> nth j (list_set l i a) d = nth j l d.
Proof.
  induction l as [|x l IH]; intros [|i] [|j] a d H; cbn [list_set nth]; try reflexivity; try lia.
  apply IH. lia.
Qed.

Lemma list_set_list_set : forall {A} (l : list A) i a b, list_set (list_set l i a) i b = list_set l i b.
Proof. induction l as [|x l IH]; intros [|i] a b; cbn [list_set]; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma list_set_nth_id : forall {A} (l : list A) i d, list_set l i (nth i l d) = l.
Proof. induction l as [|x l IH]; intros i d; cbn; [reflexivity|]. destruct i; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma list_set_app_l : forall {A} (l l' : list A) i a, (i < length l)%nat -> list_set (l ++ l') i a = list_set l i a ++ l'.
Proof.
  induction l as [|x l IH]; intros l' i a Hi; cbn in *; [lia|]. destruct i; [reflexivity|]. rewrite IH by lia. reflexivity.
Qed.

Lemma map_list_set : forall {A B} (f : A -> B) (l : list A) i a, map f (list_set l i a) = list_set (map f l) i (f a).
Proof. induction l as [|x l IH]; intros [|i] a; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Section GWP.
Context {ptr : Type}.

Definition ok_bg (X : @blocks ptr) (n : Z) : Prop :=
  (length X < BG_NBLK)%nat /\ 0 <= n <= BG_BSZ /\ Forall (fun xb => 0 <= snd xb <= BG_BSZ) X.

Fixpoint gwp {A} (t : btree ptr A) (X : blocks) (Q : A -> blocks -> Prop) : Prop :=
  match t with
  | TRet a => Q a X
  | TUnr => False
  | TMalloc n k => ok_bg X n /\ k None = TUnr /\ forall p, ~ In p (map fst X) -> gwp (k (Some p)) ((p, n) :: X) Q
  | TFree p k => exists m X', Permutation X ((p, m) :: X') /\ gwp k X' Q
  end.

Lemma gwp_mono : forall {A} (t : btree ptr A) X (Q Q' : A -> blocks -> Prop),
  gwp t X Q -> (forall a X', Q a X' -> Q' a X') -> gwp t X Q'.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH]; intros X Q Q' H HQ; cbn [gwp] in *.
  - apply HQ. exact H.
  - exact H.
  - destruct H as (Hn & Hk & H). split; [exact Hn|]. split; [exact Hk|]. intros q Hq. eapply IH; [apply H; exact Hq|exact HQ].
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. eapply IH; [exact H|exact HQ].
Qed.

Lemma gwp_bind : forall {A B} (m : btree ptr A) (f : A -> btree ptr B) X Q,
  gwp m X (fun a X' => gwp (f a) X' Q) -> gwp (tbind m f) X Q.
Proof.
  intros A B m. induction m as [a| |n k IH|p k IH]; intros f X Q H; cbn [gwp tbind] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & Hk & H). split; [exact Hn|]. split; [rewrite Hk; reflexivity|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. apply IH. exact H.
Qed.

End GWP.

Section Inv.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Definition bg_ok (b : BN) : Prop :=
  limbs (bn_buf b) /\ (bn_top b <= bn_dmax b)%nat /\ Z.of_nat (bn_dmax b) <= BG_DMAX /\ (bn_flags b = 0 \/ bn_flags b = 1).

Definition bg_okv (b : BN) : Prop := limbs (bn_buf b) /\ (bn_top b <= bn_dmax b)%nat.

Lemma bg_ok_okv : forall b, bg_ok b -> bg_okv b.
Proof. intros b (H1 & H2 & _). split; assumption. Qed.

Lemma bg_ok_bn_ok : forall b, bg_ok b -> bn_ok b.
Proof. intros b (H1 & H2 & H3 & H4). unfold bn_ok, DMAX_MAX. unfold BG_DMAX in H3. repeat split; try assumption. lia. Qed.

Lemma bg_ok_nil : forall f, f = 0 \/ f = 1 -> bg_ok (bn_nil f).
Proof. intros f Hf. unfold bg_ok, bn_nil, bn_dmax, BG_DMAX. cbn. split; [constructor|]. split; [lia|]. split; [lia|exact Hf]. Qed.

Fixpoint nondecr (l : list nat) : Prop :=
  match l with
  | [] => True
  | x :: l' => match l' with [] => True | y :: _ => (x <= y)%nat end /\ nondecr l'
  end.

Definition ctx_wf (c : bg_ctx ptr) : Prop :=
  gx_err_stack c = 0%nat /\ gx_too_many c = false /\ gx_pused c = gx_used c
  /\ (gx_used c <= BN_CTX_POOL_SIZE * length (gx_items c))%nat /\ (length (gx_items c) <= 3)%nat
  /\ gx_current c = (if (gx_used c =? 0)%nat then None else Some ((gx_used c - 1) / BN_CTX_POOL_SIZE)%nat)
  /\ nondecr (gx_frames c ++ [gx_used c])
  /\ ((gx_ssize c = 0%nat /\ gx_frames c = [] /\ gx_indexes c = None)
      \/ (gx_ssize c = BG_DEPTH /\ gx_indexes c <> None /\ (length (gx_frames c) <= BG_DEPTH)%nat)).

Definition st_wf (s : ST) : Prop :=
  length (st_bns s) = (NFIX + BN_CTX_POOL_SIZE * length (gx_items (st_ctx s)))%nat
  /\ (forall r, (r < length (st_bns s))%nat -> r <> ROne -> bg_ok (getbn r s))
  /\ getbn ROne s = bn_const_one
  /\ ctx_wf (st_ctx s).

Definition live (r : bnref) (s : ST) : Prop := (r < NFIX + gx_used (st_ctx s))%nat.

Definition blocks_of (s : ST) : blocks :=
  concat (map bn_blocks (st_bns s)) ++ map (fun p => (p, POOL_ITEM_BYTES)) (gx_items (st_ctx s))
  ++ opt_block (gx_indexes (st_ctx s)) (4 * Z.of_nat BN_CTX_START_FRAMES).

Definition own (s : ST) (F X : blocks) : Prop :=
  Permutation X (blocks_of s ++ F) /\ (length F <= BG_NF)%nat /\ Forall (fun xb : ptr * Z => 0 <= snd xb <= BG_BSZ) F.

Lemma st_wf_length : forall s, st_wf s -> (length (st_bns s) <= NFIX + BG_POOL)%nat.
Proof. intros s (E & _ & _ & (_ & _ & _ & _ & Hi & _)). rewrite E. unfold BG_POOL, BN_CTX_POOL_SIZE in *. lia. Qed.

Lemma live_valid : forall r s, st_wf s -> live r s -> (r < length (st_bns s))%nat.
Proof. intros r s (E & _ & _ & (_ & _ & _ & Hu & _)) Hl. unfold live in Hl. rewrite E. lia. Qed.

Lemma st_wf_ok : forall r s, st_wf s -> (r < length (st_bns s))%nat -> r <> ROne -> bg_ok (getbn r s).
Proof. intros r s (_ & H & _) Hr Hn. apply H; assumption. Qed.

Lemma st_wf_okv : forall r s, st_wf s -> (r < length (st_bns s))%nat -> bg_okv (getbn r s).
Proof.
  intros r s Hs Hr. destruct (Nat.eq_dec r ROne) as [->|Hn].
  - destruct Hs as (_ & _ & E & _). rewrite E. unfold bg_okv, bn_const_one, bn_dmax. cbn.
    split; [|lia]. constructor; [unfold limb, BW; lia|constructor].
  - apply bg_ok_okv, st_wf_ok; assumption.
Qed.

Lemma getbn_setbn_same : forall r b (s : ST), (r < length (st_bns s))%nat -> getbn r (setbn r b s) = b.
Proof. intros r b s Hr. unfold getbn, setbn, set_bns. cbn [st_bns]. apply nth_list_set_same. exact Hr. Qed.

Lemma getbn_setbn_other : forall r r' b (s : ST), r <> r' -> getbn r' (setbn r b s) = getbn r' s.
Proof. intros r r' b s Hne. unfold getbn, setbn, set_bns. cbn [st_bns]. apply nth_list_set_other. exact Hne. Qed.

Lemma setbn_setbn_same : forall r b1 b2 (s : ST), setbn r b2 (setbn r b1 s) = setbn r b2 s.
Proof. intros r b1 b2 s. unfold setbn, set_bns. cbn [st_bns st_ctx st_ri st_n0 st_rbits st_rshift]. rewrite list_set_list_set. reflexivity. Qed.

Lemma setbn_getbn_id : forall r (s : ST), setbn r (getbn r s) s = s.
Proof. intros r s. destruct s as [l c x1 x2 x3 x4]. unfold setbn, set_bns, getbn. cbn [st_bns st_ctx st_ri st_n0 st_rbits st_rshift]. rewrite list_set_nth_id. reflexivity. Qed.

Lemma length_setbn : forall r b (s : ST), length (st_bns (setbn r b s)) = length (st_bns s).
Proof. intros. unfold setbn, set_bns. cbn [st_bns]. apply list_set_length. Qed.

Lemma st_ctx_setbn : forall r b (s : ST), st_ctx (setbn r b s) = st_ctx s.
Proof. reflexivity. Qed.

Lemma st_wf_setbn : forall r b (s : ST), st_wf s -> r <> ROne -> bg_ok b -> st_wf (setbn r b s).
Proof.
  intros r b s (E & Hok & Hone & Hc) Hn Hb. unfold st_wf. rewrite length_setbn, st_ctx_setbn.
  split; [exact E|]. split; [|split; [|exact Hc]].
  - intros r' Hr' Hn'. destruct (Nat.eq_dec r r') as [<-|Hne].
    + rewrite getbn_setbn_same by exact Hr'. exact Hb.
    + rewrite getbn_setbn_other by exact Hne. apply Hok; assumption.
  - rewrite getbn_setbn_other by exact Hn. exact Hone.
Qed.

Lemma concat_blocks_pick : forall (l : list BN) i, (i < length l)%nat ->
  exists R, Permutation (concat (map bn_blocks l)) (bn_blocks (nth i l (bn_nil 0)) ++ R) /\
            forall b, Permutation (concat (map bn_blocks (list_set l i b))) (bn_blocks b ++ R).
Proof.
  induction l as [|x l IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i].
  - exists (concat (map bn_blocks l)). cbn [nth map concat list_set]. split; [apply Permutation_refl|]. intros b. apply Permutation_refl.
  - destruct (IH i ltac:(lia)) as (R & H1 & H2). exists (bn_blocks x ++ R). cbn [nth map concat list_set]. split.
    + eapply Permutation_trans; [apply Permutation_app_head; exact H1|]. apply Permutation_app_swap_app.
    + intros b. eapply Permutation_trans; [apply Permutation_app_head; apply H2|]. apply Permutation_app_swap_app.
Qed.

Lemma blocks_setbn : forall r (s : ST), (r < length (st_bns s))%nat ->
  exists R, Permutation (blocks_of s) (bn_blocks (getbn r s) ++ R) /\
            forall b, Permutation (blocks_of (setbn r b s)) (bn_blocks b ++ R).
Proof.
  intros r s Hr. destruct (concat_blocks_pick (st_bns s) r Hr) as (R & H1 & H2).
  set (T := map (fun p => (p, POOL_ITEM_BYTES)) (gx_items (st_ctx s)) ++ opt_block (gx_indexes (st_ctx s)) (4 * Z.of_nat BN_CTX_START_FRAMES)).
  exists (R ++ T). unfold blocks_of. fold T. split.
  - rewrite app_assoc. apply Permutation_app_tail. exact H1.
  - intros b. unfold setbn, set_bns. cbn [st_bns st_ctx]. fold T. rewrite app_assoc. apply Permutation_app_tail. apply H2.
Qed.

Lemma bn_blocks_same : forall (b b' : BN), bn_d b' = bn_d b -> length (bn_buf b') = length (bn_buf b) -> bn_blocks b' = bn_blocks b.
Proof. intros b b' E1 E2. unfold bn_blocks, bn_dmax. rewrite E1, E2. reflexivity. Qed.

Lemma blocks_of_setbn_same : forall r b (s : ST), (r < length (st_bns s))%nat ->
  bn_blocks b = bn_blocks (getbn r s) -> blocks_of (setbn r b s) = blocks_of s.
Proof.
  intros r b s Hr E. unfold blocks_of, setbn, set_bns. cbn [st_bns st_ctx]. f_equal. f_equal.
  rewrite map_list_set, E. unfold getbn. rewrite <- (map_nth bn_blocks). apply list_set_nth_id.
Qed.

Lemma bn_blocks_length : forall b : BN, (length (bn_blocks b) <= 1)%nat.
Proof. intros b. unfold bn_blocks. destruct (bn_d b); cbn; lia. Qed.

Lemma concat_blocks_length : forall l : list BN, (length (concat (map bn_blocks l)) <= length l)%nat.
Proof.
  induction l as [|x l IH]; cbn [map concat length]; [lia|]. rewrite length_app. pose proof (bn_blocks_length x). lia.
Qed.

Lemma bn_blocks_size : forall b : BN, Z.of_nat (bn_dmax b) <= BG_DMAX -> Forall (fun xb : ptr * Z => 0 <= snd xb <= BG_BSZ) (bn_blocks b).
Proof.
  intros b Hd. unfold bn_blocks. destruct (bn_d b); constructor; [|constructor].
  cbn [snd]. unfold BG_BSZ, BG_DMAX in *. lia.
Qed.

Lemma st_wf_blocks : forall s, st_wf s ->
  (length (blocks_of s) <= NFIX + BG_POOL + 3)%nat /\ Forall (fun xb => 0 <= snd xb <= BG_BSZ) (blocks_of s).
Proof.
  intros s Hs. pose proof (st_wf_length s Hs) as Hlen. pose proof Hs as (E & Hok & Hone & Hc).
  destruct Hc as (_ & _ & _ & _ & Hi & _).
  assert (Hf : Forall (fun xb : ptr * Z => 0 <= snd xb <= BG_BSZ) (concat (map bn_blocks (st_bns s)))).
  { apply Forall_concat. apply Forall_map. apply Forall_forall. intros b Hin.
    destruct (In_nth _ _ (bn_nil 0) Hin) as (r & Hr & Eb). destruct (Nat.eq_dec r ROne) as [->|Hn].
    - fold (getbn ROne s) in Eb. rewrite Hone in Eb. subst b. constructor.
    - fold (getbn r s) in Eb. subst b. apply bn_blocks_size. destruct (Hok r Hr Hn) as (_ & _ & Hd & _). exact Hd. }

  assert (Hcnt : (length (concat (map bn_blocks (st_bns s))) <= length (st_bns s) - 1)%nat).
  { assert (Hone' : nth ROne (st_bns s) (bn_nil 0) = bn_const_one) by exact Hone.
    assert (HR : (ROne < length (st_bns s))%nat) by (rewrite E; unfold ROne, NFIX; lia).
    destruct (concat_blocks_pick (st_bns s) ROne HR) as (R & H1 & H2).
    rewrite Hone' in H1. cbn [bn_blocks bn_const_one bn_d app] in H1.
    specialize (H2 (bn_nil 0)). cbn [bn_blocks bn_nil bn_d app] in H2.
    rewrite (Permutation_length H1), <- (Permutation_length H2).

    assert (Hsplit : list_set (st_bns s) ROne (bn_nil 0) = firstn ROne (st_bns s) ++ bn_nil 0 :: skipn (S ROne) (st_bns s)).
    { clear -HR. revert HR. generalize (st_bns s). generalize ROne. induction b as [|n IH]; intros l Hl; destruct l as [|x l]; cbn in *; try lia; [reflexivity|].
      rewrite IH by lia. reflexivity. }
    rewrite Hsplit, map_app, concat_app, length_app. cbn [map concat bn_blocks bn_nil bn_d app].
    pose proof (concat_blocks_length (firstn ROne (st_bns s))). pose proof (concat_blocks_length (skipn (S ROne) (st_bns s))).
    rewrite firstn_length_le in H by lia. rewrite length_skipn in H0. lia. }
  split.
  - unfold blocks_of. rewrite !length_app, length_map.
    assert ((length (opt_block (gx_indexes (st_ctx s)) (4 * Z.of_nat BN_CTX_START_FRAMES)) <= 1)%nat) by (destruct (gx_indexes (st_ctx s)); cbn; lia).
    unfold BG_POOL, NFIX in *. lia.
  - unfold blocks_of. rewrite !Forall_app. split; [exact Hf|]. split.
    + apply Forall_map. apply Forall_forall. intros p _. cbn [snd]. unfold POOL_ITEM_BYTES, BG_BSZ. lia.
    + destruct (gx_indexes (st_ctx s)); constructor; [|constructor]. cbn [snd]. unfold BG_BSZ, BN_CTX_START_FRAMES. lia.
Qed.

Lemma own_ok_bg : forall s F X n, st_wf s -> own s F X -> 0 <= n <= BG_BSZ -> ok_bg X n.
Proof.
  intros s F X n Hs (HP & HF & HFs) Hn. destruct (st_wf_blocks s Hs) as [Hl Hf]. unfold ok_bg.
  split; [|split; [exact Hn|]].
  - rewrite (Permutation_length HP), length_app. unfold BG_NBLK, BG_NF, BG_POOL, NFIX in *. lia.
  - eapply Permutation_Forall; [apply Permutation_sym; exact HP|]. rewrite Forall_app. split; assumption.
Qed.

Definition std_flags (r : bnref) : Z := if (r <? 5)%nat then BN_FLG_MALLOCED else 0.
Definition fl_ok (s : ST) : Prop :=
  forall r, (r < length (st_bns s))%nat -> r <> ROne -> bn_flags (getbn r s) = std_flags r.

Lemma fl_ok_setbn : forall r b (s : ST), fl_ok s -> bn_flags b = bn_flags (getbn r s) -> fl_ok (setbn r b s).
Proof.
  intros r b s H E r' Hr' Hn'. rewrite length_setbn in Hr'. destruct (Nat.eq_dec r r') as [<-|Hne].
  - rewrite getbn_setbn_same by exact Hr'. rewrite E. apply H; assumption.
  - rewrite getbn_setbn_other by exact Hne. apply H; assumption.
Qed.

Lemma fl_ok_set_ctx : forall c (s : ST), fl_ok s -> fl_ok (set_ctx c s).
Proof. intros c s H r Hr Hn. exact (H r Hr Hn). Qed.

Lemma fl_ok_app_nil : forall (s : ST) k, fl_ok s -> (NFIX <= length (st_bns s))%nat ->
  fl_ok (set_bns (st_bns s ++ repeat (bn_nil 0) k) s).
Proof.
  intros s k H Hl r Hr Hn. unfold getbn in *. cbn [set_bns st_bns] in *. rewrite length_app, repeat_length in Hr.
  destruct (Nat.lt_ge_cases r (length (st_bns s))) as [Hlt|Hge].
  - rewrite app_nth1 by exact Hlt. apply H; assumption.
  - rewrite app_nth2 by exact Hge. rewrite nth_repeat_lt by lia. unfold std_flags, NFIX in *. cbn [bn_nil bn_flags].
    destruct (Nat.ltb_spec r 5); [lia|reflexivity].
Qed.

Lemma fl_ok_flags0 : forall r (s : ST), fl_ok s -> (5 <= r)%nat -> (r < length (st_bns s))%nat -> r <> ROne -> bn_flags (getbn r s) = 0.
Proof. intros r s H H5 Hr Hn. rewrite (H r Hr Hn). unfold std_flags. destruct (Nat.ltb_spec r 5); [lia|reflexivity]. Qed.

Lemma fl_ok_flags1 : forall r (s : ST), fl_ok s -> (r < 5)%nat -> (r < length (st_bns s))%nat -> bn_flags (getbn r s) = BN_FLG_MALLOCED.
Proof.
  intros r s H H5 Hr. rewrite (H r Hr ltac:(unfold ROne; lia)). unfold std_flags. destruct (Nat.ltb_spec r 5); [reflexivity|lia].
Qed.

Definition hoareG {A} (F : blocks) (F' : A -> blocks) (s : ST) (m : BM (M:=btree ptr) (ptr:=ptr) A) (Q : A -> ST -> Prop) : Prop :=
  forall X, st_wf s -> fl_ok s -> own s F X ->
    gwp (m s) X (fun p X' => st_wf (snd p) /\ fl_ok (snd p) /\ own (snd p) (F' (fst p)) X' /\ Q (fst p) (snd p)).

Definition hoare {A} (F : blocks) (s : ST) (m : BM (M:=btree ptr) (ptr:=ptr) A) (Q : A -> ST -> Prop) : Prop :=
  hoareG F (fun _ => F) s m Q.

Lemma hoareG_wf : forall {A} F F' s (m : BM A) Q, (st_wf s -> hoareG F F' s m Q) -> hoareG F F' s m Q.
Proof. intros A F F' s m Q H X Hs Hf Ho. apply H; assumption. Qed.

Lemma hoare_wf : forall {A} F s (m : BM A) Q, (st_wf s -> hoare F s m Q) -> hoare F s m Q.
Proof. intros. apply hoareG_wf. assumption. Qed.

Lemma hoareG_fl : forall {A} F F' s (m : BM A) Q, (fl_ok s -> hoareG F F' s m Q) -> hoareG F F' s m Q.
Proof. intros A F F' s m Q H X Hs Hf Ho. apply H; assumption. Qed.

Lemma hoare_fl : forall {A} F s (m : BM A) Q, (fl_ok s -> hoare F s m Q) -> hoare F s m Q.
Proof. intros. apply hoareG_fl. assumption. Qed.

Lemma hoareG_ret : forall {A} F (F' : A -> blocks) (a : A) s (Q : A -> ST -> Prop), F' a = F -> Q a s -> hoareG F F' s (bret ops a) Q.
Proof. intros A F F' a s Q E H X Hs Hf Ho. cbn. rewrite E. auto. Qed.

Lemma hoare_ret : forall {A} F (a : A) s (Q : A -> ST -> Prop), Q a s -> hoare F s (bret ops a) Q.
Proof. intros. apply hoareG_ret; [reflexivity|assumption]. Qed.

Lemma hoareG_bind : forall {A B} F F1 F2 (m : BM A) (f : A -> BM B) s (R : A -> ST -> Prop) Q,
  hoareG F F1 s m R -> (forall a s', st_wf s' -> R a s' -> hoareG (F1 a) F2 s' (f a) Q) ->
  hoareG F F2 s (bbind ops m f) Q.
Proof.
  intros A B F F1 F2 m f s R Q Hm Hf X Hs Hfl Ho. unfold bbind. cbn [bind tree_ops]. apply gwp_bind.
  eapply gwp_mono; [apply Hm; assumption|]. intros [a s'] X' (Hs' & Hfl' & Ho' & HR). cbn [fst snd] in *.
  apply Hf; assumption.
Qed.

Lemma hoare_bind : forall {A B} F (m : BM A) (f : A -> BM B) s (R : A -> ST -> Prop) Q,
  hoare F s m R -> (forall a s', st_wf s' -> R a s' -> hoare F s' (f a) Q) -> hoare F s (bbind ops m f) Q.
Proof. intros. eapply hoareG_bind; eassumption. Qed.

Lemma hoareG_mono : forall {A} F F' s (m : BM A) (Q Q' : A -> ST -> Prop),
  hoareG F F' s m Q -> (forall a s', st_wf s' -> Q a s' -> Q' a s') -> hoareG F F' s m Q'.
Proof.
  intros A F F' s m Q Q' H HQ X Hs Hf Ho. eapply gwp_mono; [apply H; assumption|].
  intros [a s'] X' (Hs' & Hf' & Ho' & Hq). cbn [fst snd] in *. auto.
Qed.

Lemma hoare_mono : forall {A} F s (m : BM A) (Q Q' : A -> ST -> Prop),
  hoare F s m Q -> (forall a s', st_wf s' -> Q a s' -> Q' a s') -> hoare F s m Q'.
Proof. intros. eapply hoareG_mono; eassumption. Qed.

Lemma hoare_get : forall r F s (Q : BN -> ST -> Prop), Q (getbn r s) s -> hoare F s (bget ops r) Q.
Proof. intros. apply hoare_ret. assumption. Qed.

Lemma hoare_set : forall r b F s (Q : unit -> ST -> Prop),
  (r < length (st_bns s))%nat -> r <> ROne -> bg_ok b ->
  bn_d b = bn_d (getbn r s) -> length (bn_buf b) = length (bn_buf (getbn r s)) ->
  Q tt (setbn r b s) -> bn_flags b = bn_flags (getbn r s) -> hoare F s (bset ops r b) Q.
Proof.
  intros r b F s Q Hr Hn Hb Ed El HQ Ef X Hs Hf (HP & HF). cbn. split; [apply st_wf_setbn; assumption|].
  split; [apply fl_ok_setbn; assumption|]. split; [|exact HQ].
  split; [|exact HF]. rewrite blocks_of_setbn_same; [exact HP|exact Hr|apply bn_blocks_same; assumption].
Qed.

Lemma hoare_setmont : forall ri n0 F s (Q : unit -> ST -> Prop), Q tt (set_mont ri n0 s) -> hoare F s (bsetmont ops ri n0) Q.
Proof. intros ri n0 F s Q HQ X Hs Hf Ho. cbn. split; [exact Hs|]. split; [exact Hf|]. split; [exact Ho|exact HQ]. Qed.

Lemma hoare_setrecp : forall bits sh F s (Q : unit -> ST -> Prop), Q tt (set_recp bits sh s) -> hoare F s (bsetrecp ops bits sh) Q.
Proof. intros bits sh F s Q HQ X Hs Hf Ho. cbn. split; [exact Hs|]. split; [exact Hf|]. split; [exact Ho|exact HQ]. Qed.

End Inv.
