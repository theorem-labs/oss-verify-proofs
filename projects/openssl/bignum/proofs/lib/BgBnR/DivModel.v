(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BnModel BnTree BgState BgInv BgLib BgArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section DivModel.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

Lemma leaves_mono' : forall {A} (t : btree ptr A) (phi psi : A -> Prop), (forall a, phi a -> psi a) -> leaves t phi -> leaves t psi.
Proof. intros A t phi psi H. induction t as [a| |n k IH|p k IH]; cbn [leaves]; auto. Qed.

Lemma getbn_set_ctx : forall r c (s : ST), getbn r (set_ctx c s) = getbn r s.
Proof. reflexivity. Qed.

Lemma getbn_set_bns_app_nil : forall r (s : ST) n, getbn r (set_bns (st_bns s ++ repeat (bn_nil 0) n) s) = getbn r s.
Proof.
  intros r s n. unfold getbn, set_bns. cbn [st_bns].
  destruct (Nat.lt_ge_cases r (length (st_bns s))) as [LT|GE].
  - apply app_nth1. exact LT.
  - rewrite app_nth2 by exact GE. rewrite (nth_overflow (st_bns s)) by exact GE.
    destruct (Nat.lt_ge_cases (r - length (st_bns s)) n) as [L2|G2].
    + apply nth_repeat_lt. exact L2.
    + apply nth_overflow. rewrite repeat_length. exact G2.
Qed.

Lemma getbn_set_ctx_setbn_same : forall r b c (s : ST), (r < length (st_bns s))%nat -> getbn r (set_ctx c (setbn r b s)) = b.
Proof. intros r b c s H. rewrite getbn_set_ctx. apply getbn_setbn_same. exact H. Qed.

Definition start_leaf (s : ST) (a : unit * ST) : Prop :=
  st_bns (snd a) = st_bns s /\ gx_pused (st_ctx (snd a)) = gx_pused (st_ctx s) /\ gx_used (st_ctx (snd a)) = gx_used (st_ctx s)
  /\ gx_items (st_ctx (snd a)) = gx_items (st_ctx s).

Lemma BN_CTX_start_leaves : forall s : ST, leaves (BN_CTX_start ops s) (start_leaf s).
Proof.
  intros s. unfold BN_CTX_start, bbind, bgetctx, bsetctx, bunr, bmalloc, bfree_opt, bfree, bret.
  cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd].
  destruct (negb (gx_err_stack (st_ctx s) =? 0)%nat || gx_too_many (st_ctx s)); [exact I|].
  destruct (length (gx_frames (st_ctx s)) =? gx_ssize (st_ctx s))%nat.
  - destruct (negb (gx_ssize (st_ctx s) =? 0)%nat); [exact I|].
    cbn [tbind leaves]. intros [p|]; [|exact I].
    destruct (gx_indexes (st_ctx s)) as [q|]; cbn [tbind leaves bret ret tree_ops fst snd]; unfold start_leaf; cbn; auto.
  - cbn [leaves]. unfold start_leaf. cbn. auto.
Qed.

Definition get_leaf (s : ST) (a : bnref * ST) : Prop :=
  fst a = RPool (gx_pused (st_ctx s))
  /\ gx_pused (st_ctx (snd a)) = S (gx_pused (st_ctx s)) /\ gx_used (st_ctx (snd a)) = S (gx_used (st_ctx s))
  /\ (forall r, r <> RPool (gx_pused (st_ctx s)) -> getbn r (snd a) = getbn r s)
  /\ bn_top (getbn (fst a) (snd a)) = 0%nat /\ bn_neg (getbn (fst a) (snd a)) = false.

Lemma BN_CTX_get_leaves : forall s : ST,
  (gx_pused (st_ctx s) <= BN_CTX_POOL_SIZE * length (gx_items (st_ctx s)))%nat ->
  length (st_bns s) = (NFIX + BN_CTX_POOL_SIZE * length (gx_items (st_ctx s)))%nat ->
  leaves (BN_CTX_get ops s) (get_leaf s).
Proof.
  intros s HP HL. unfold BN_CTX_get, bbind, bgetctx, bsetctx, bunr, bmalloc, bget, bset, bret, bgetst, bsetbns.
  cbn [bind ret unreachable lib_malloc tree_ops tbind fst snd].
  destruct (negb (gx_err_stack (st_ctx s) =? 0)%nat || gx_too_many (st_ctx s)); [exact I|].
  set (c := st_ctx s) in *. set (i := gx_pused c) in *.
  destruct (i =? BN_CTX_POOL_SIZE * length (gx_items c))%nat eqn:EQ.
  - destruct (3 <=? length (gx_items c))%nat; [exact I|].
    cbn [tbind leaves]. intros [p|]; [|exact I]. cbn [tbind leaves fst snd].
    apply Nat.eqb_eq in EQ.
    unfold get_leaf. cbn [fst snd set_ctx st_ctx gx_pused gx_used]. fold c. fold i.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    + intros r Hr. unfold getbn at 1. cbn [setbn set_bns set_ctx st_bns].
      rewrite nth_list_set_other by (intros E; apply Hr; symmetry; exact E).
      exact (getbn_set_bns_app_nil r s BN_CTX_POOL_SIZE).
    + rewrite !getbn_set_ctx_setbn_same by (cbn [set_ctx set_bns st_bns]; rewrite length_app, repeat_length, HL; unfold RPool, BN_CTX_POOL_SIZE in *; lia).
      cbn [bn_zero_pure bn_top bn_neg]. split; reflexivity.
  - cbn [tbind leaves fst snd].
    apply Nat.eqb_neq in EQ.
    unfold get_leaf. cbn [fst snd set_ctx st_ctx gx_pused gx_used]. fold c. fold i.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    + intros r Hr. unfold getbn at 1. cbn [setbn set_bns set_ctx st_bns].
      rewrite nth_list_set_other by (intros E; apply Hr; symmetry; exact E). reflexivity.
    + rewrite !getbn_set_ctx_setbn_same by (cbn [set_ctx st_bns]; rewrite HL; unfold RPool, BN_CTX_POOL_SIZE in *; lia).
      cbn [bn_zero_pure bn_top bn_neg]. split; reflexivity.
Qed.

Lemma st_wf_get_pre : forall s : ST, st_wf s ->
  (gx_pused (st_ctx s) <= BN_CTX_POOL_SIZE * length (gx_items (st_ctx s)))%nat
  /\ length (st_bns s) = (NFIX + BN_CTX_POOL_SIZE * length (gx_items (st_ctx s)))%nat
  /\ gx_pused (st_ctx s) = gx_used (st_ctx s).
Proof. intros s (EL & _ & _ & (_ & _ & E3 & E4 & _)). rewrite E3. auto. Qed.

Definition copy_leaf (ra rb : bnref) (s : ST) (a : unit * ST) : Prop :=
  let b := getbn rb s in
  (forall r, ra <> r -> getbn r (snd a) = getbn r s)
  /\ bn_top (getbn ra (snd a)) = bn_top b /\ bn_neg (getbn ra (snd a)) = bn_neg b
  /\ firstn (bn_top b) (bn_buf (getbn ra (snd a))) = firstn (bn_top b) (bn_buf b)
  /\ (bn_top b <= bn_dmax (getbn ra (snd a)))%nat
  /\ st_ctx (snd a) = st_ctx s.

Definition wexp_leaf2 (r : bnref) (words : nat) (s : ST) (a : unit * ST) : Prop :=
  (forall r', r <> r' -> getbn r' (snd a) = getbn r' s)
  /\ bn_top (getbn r (snd a)) = bn_top (getbn r s) /\ bn_neg (getbn r (snd a)) = bn_neg (getbn r s)
  /\ bn_flags (getbn r (snd a)) = bn_flags (getbn r s)
  /\ firstn (bn_top (getbn r s)) (bn_buf (getbn r (snd a))) = firstn (bn_top (getbn r s)) (bn_buf (getbn r s))
  /\ (words <= bn_dmax (getbn r (snd a)))%nat
  /\ st_ctx (snd a) = st_ctx s /\ length (st_bns (snd a)) = length (st_bns s).

Lemma bn_wexpand_leaves2 : forall r words (s : ST), (r < length (st_bns s))%nat -> (bn_top (getbn r s) <= bn_dmax (getbn r s))%nat ->
  leaves (bn_wexpand ops r words s) (wexp_leaf2 r words s).
Proof.
  intros r words s HV HT. unfold bn_wexpand, bbind, bget, bret, bunr, bmalloc, bfree_opt, bset, bfree, has_flag.
  cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd].
  set (b := getbn r s) in *.
  destruct (Nat.leb_spec words (bn_dmax b)) as [LE|GT].
  { cbn [leaves]. unfold wexp_leaf2. cbn [snd]. fold b. auto 10. }
  destruct (BN_WORDS_MAX <? Z.of_nat words); [exact I|].
  destruct (512 <? Z.of_nat words); [exact I|].
  destruct (negb (Z.land (bn_flags b) BN_FLG_STATIC_DATA =? 0)); [exact I|].
  destruct (negb (Z.land (bn_flags b) BN_FLG_SECURE =? 0)); [exact I|].
  cbn [tbind leaves]. intros [p|]; [|exact I].
  assert (NEW : wexp_leaf2 r words s (tt, setbn r (mkBN (Some p) (firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)) (bn_top b) (bn_neg b) (bn_flags b)) s)).
  { unfold wexp_leaf2. cbn [snd]. rewrite getbn_setbn_same by exact HV. cbn [bn_top bn_neg bn_flags bn_buf]. fold b.
    unfold bn_dmax in *. cbn [bn_buf].
    split; [intros r' Hne; apply getbn_setbn_other; exact Hne|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split. { rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn, Nat.min_l by exact HT.
             rewrite Nat.sub_diag. cbn [firstn]. apply app_nil_r. }
    split; [rewrite length_app, length_firstn, repeat_length; lia|].
    split; [apply st_ctx_setbn| apply length_setbn]. }
  destruct (bn_d b) as [q|]; cbn [tbind leaves]; exact NEW.
Qed.

Lemma BN_copy_leaves : forall ra rb (s : ST), ra <> rb -> (ra < length (st_bns s))%nat ->
  (bn_top (getbn ra s) <= bn_dmax (getbn ra s))%nat -> (bn_top (getbn rb s) <= bn_dmax (getbn rb s))%nat ->
  leaves (BN_copy ops ra rb s) (copy_leaf ra rb s).
Proof.
  intros ra rb s NE HV HTa HTb. unfold BN_copy. unfold bbind at 1. unfold bget at 1. cbn [bind ret tree_ops tbind fst snd].
  set (b := getbn rb s) in *. unfold has_flag.
  destruct (negb (Z.land (bn_flags b) BN_FLG_CONSTTIME =? 0)); [exact I|].
  replace (ra =? rb)%nat with false by (symmetry; apply Nat.eqb_neq; exact NE).
  unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
  apply leaves_bind'. eapply leaves_mono'; [|apply (bn_wexpand_leaves2 ra (bn_top b) s HV HTa)].
  intros [u s1] (W1 & W2 & W3 & W4 & W5 & WD & WC & WL). cbn [snd fst] in *. cbn [leaves].
  unfold copy_leaf. cbn [snd]. fold b.
  assert (HV1 : (ra < length (st_bns s1))%nat) by (rewrite WL; exact HV).
  rewrite getbn_setbn_same by exact HV1. cbn [bn_top bn_neg bn_buf].
  split. { intros r Hr. rewrite getbn_setbn_other by exact Hr. apply W1. exact Hr. }
  split; [reflexivity|]. split; [reflexivity|].
  unfold bn_dmax in *. cbn [bn_buf].
  split. { destruct (Nat.ltb_spec 0 (bn_top b)) as [P|Z0].
           - apply firstn_splice_0; [rewrite length_firstn; lia | lia].
           - replace (bn_top b) with 0%nat by lia. reflexivity. }
  split. { destruct (0 <? bn_top b)%nat; [rewrite splice_length; [exact WD| rewrite length_firstn; lia] | exact WD]. }
  rewrite st_ctx_setbn. exact WC.
Qed.

Lemma lshift_limbs_len : forall l lb m, length (fst (lshift_limbs l lb m)) = length l.
Proof.
  induction l as [|x l IH]; intros lb m; [reflexivity|]. cbn [lshift_limbs].
  specialize (IH lb (if lb =? 0 then 0 else shrw x (64 - lb))). destruct (lshift_limbs l lb (if lb =? 0 then 0 else shrw x (64 - lb))) as [r mo].
  cbn [fst length] in *. rewrite IH. reflexivity.
Qed.

Definition lsh_res (bx : BN) (n : Z) : list Z :=
  if (bn_top bx =? 0)%nat then [0] else fst (lshift_limbs (firstn (bn_top bx) (bn_buf bx)) n 0) ++ [snd (lshift_limbs (firstn (bn_top bx) (bn_buf bx)) n 0)].

Definition lsh_leaf (rr rx : bnref) (n : Z) (s : ST) (a : unit * ST) : Prop :=
  let bx := getbn rx s in
  (forall r, rr <> r -> getbn r (snd a) = getbn r s)
  /\ bn_top (getbn rr (snd a)) = (bn_top bx + 1)%nat /\ bn_neg (getbn rr (snd a)) = bn_neg bx
  /\ firstn (bn_top bx + 1) (bn_buf (getbn rr (snd a))) = lsh_res bx n
  /\ (bn_top bx + 1 <= bn_dmax (getbn rr (snd a)))%nat
  /\ st_ctx (snd a) = st_ctx s.

Lemma bn_lshift_leaves : forall rr rx n (s : ST), rr <> rx -> 0 <= n < 64 -> (rr < length (st_bns s))%nat ->
  (bn_top (getbn rr s) <= bn_dmax (getbn rr s))%nat -> (bn_top (getbn rx s) <= bn_dmax (getbn rx s))%nat ->
  leaves (bn_lshift_fixed_top ops rr rx n s) (lsh_leaf rr rx n s).
Proof.
  intros rr rx n s NE Hn HV HTr HTx. unfold bn_lshift_fixed_top.
  replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Z.to_nat (n / 64)) with 0%nat by (rewrite Z.div_small by lia; reflexivity).
  replace (n mod 64) with n by (symmetry; apply Z.mod_small; lia).
  cbn [Nat.eqb]. unfold bbind at 1. unfold bget at 1. cbn [bind ret tree_ops tbind fst snd].
  set (bx := getbn rx s) in *.
  unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
  apply leaves_bind'. eapply leaves_mono'; [|apply (bn_wexpand_leaves2 rr (bn_top bx + 0 + 1) s HV HTr)].
  intros [u s1] (W1 & W2 & W3 & W4 & W5 & WD & WC & WL). cbn [snd fst] in *. cbn [leaves].
  unfold lsh_leaf. cbn [snd]. fold bx.
  rewrite (W1 rx NE). fold bx.
  assert (HV1 : (rr < length (st_bns s1))%nat) by (rewrite WL; exact HV).
  rewrite getbn_setbn_same by exact HV1. cbn [bn_top bn_neg bn_buf].
  replace (bn_top bx + 0 + 1)%nat with (bn_top bx + 1)%nat in * by lia.
  split. { intros r Hr. rewrite getbn_setbn_other by exact Hr. apply W1. exact Hr. }
  split; [reflexivity|]. split; [reflexivity|].
  unfold bn_dmax, lsh_res in *.
  destruct (Nat.eqb_spec (bn_top bx) 0) as [Z0|NZ].
  - rewrite Z0 in *. cbn [Nat.add].
    split. { unfold upd. apply (firstn_splice_0 (bn_buf (getbn rr s1)) [0] 1); [reflexivity | lia]. }
    split; [cbn [bn_buf]; rewrite upd_length by lia; exact WD| rewrite st_ctx_setbn; exact WC].
  - pose proof (lshift_limbs_len (firstn (bn_top bx) (bn_buf bx)) n 0) as L0.
    destruct (lshift_limbs (firstn (bn_top bx) (bn_buf bx)) n 0) as [l0 mo]. cbn [fst snd] in *.
    assert (LL : length (l0 ++ [mo]) = (bn_top bx + 1)%nat) by (rewrite length_app, L0, length_firstn; cbn [length]; lia).
    split. { apply firstn_splice_0; [exact LL | lia]. }
    split; [cbn [bn_buf]; rewrite splice_length by lia; exact WD | rewrite st_ctx_setbn; exact WC].
Qed.

End DivModel.
