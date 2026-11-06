(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnLeaves.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation LS := (lstate bptr) (only parsing).

Lemma leaves_mono : forall {A} (t : btree bptr A) (phi psi : A -> Prop), (forall a, phi a -> psi a) -> leaves t phi -> leaves t psi.
Proof. intros A t phi psi H. induction t as [a| |n k IH|p k IH]; cbn [leaves]; auto. Qed.

(* [comment removed for export] *)
Lemma pused_setbn : forall r b (s : LS), cx_pused (ls_ctx (setbn r b s)) = cx_pused (ls_ctx s).
Proof. intros [| | | | |i] b s; reflexivity. Qed.
Lemma psize_setbn : forall r b (s : LS), cx_psize (ls_ctx (setbn r b s)) = cx_psize (ls_ctx s).
Proof. intros [| | | | |i] b s; reflexivity. Qed.
Lemma vals_len_setbn : forall r b (s : LS), length (cx_vals (ls_ctx (setbn r b s))) = length (cx_vals (ls_ctx s)).
Proof. intros [| | | | |i] b s; try reflexivity. cbn [setbn set_ctx ls_ctx ctx_set_vals cx_vals]. apply list_set_length. Qed.

(* [comment removed for export] *)
Definition start_leaf (ls : LS) (a : unit * LS) : Prop :=
  (forall r, getbn r (snd a) = getbn r ls) /\ cx_pused (ls_ctx (snd a)) = cx_pused (ls_ctx ls)
  /\ cx_psize (ls_ctx (snd a)) = cx_psize (ls_ctx ls) /\ cx_vals (ls_ctx (snd a)) = cx_vals (ls_ctx ls).

Lemma BN_CTX_start_leaves : forall ls : LS, leaves (BN_CTX_start (tree_ops bptr) ls) (start_leaf ls).
Proof.
  intros ls. unfold BN_CTX_start, bbind, bgetctx, bsetctx, bunr, bmalloc, bfree_opt, bfree, bret.
  cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd].
  destruct (negb (cx_err_stack (ls_ctx ls) =? 0)%nat || cx_too_many (ls_ctx ls)); [exact I|].
  assert (G : forall c', cx_vals c' = cx_vals (ls_ctx ls) -> cx_pused c' = cx_pused (ls_ctx ls) -> cx_psize c' = cx_psize (ls_ctx ls) ->
              start_leaf ls (tt, set_ctx c' ls)).
  { intros c' E1 E2 E3. unfold start_leaf. cbn [snd set_ctx ls_ctx]. split; [intros r; apply getbn_set_ctx; exact E1|]. auto. }
  destruct (length (cx_frames (ls_ctx ls)) =? cx_ssize (ls_ctx ls))%nat.
  - destruct (negb (cx_ssize (ls_ctx ls) =? 0)%nat); [exact I|].
    cbn [tbind leaves]. intros [p|]; [|exact I].
    destruct (cx_indexes (ls_ctx ls)) as [q|]; cbn [tbind leaves]; apply G; reflexivity.
  - cbn [leaves]. apply G; reflexivity.
Qed.

Definition end_leaf (ls : LS) (a : unit * LS) : Prop := forall r, getbn r (snd a) = getbn r ls.

Lemma BN_CTX_end_leaves : forall ls : LS, leaves (BN_CTX_end (tree_ops bptr) ls) (end_leaf ls).
Proof.
  intros ls. unfold BN_CTX_end, bbind, bgetctx, bsetctx, bunr, bret.
  cbn [bind ret unreachable tree_ops tbind fst snd].
  destruct (negb (cx_err_stack (ls_ctx ls) =? 0)%nat); [exact I|].
  destruct (rev (cx_frames (ls_ctx ls))) as [|fp rest]; [exact I|].
  cbn [leaves]. unfold end_leaf. cbn [snd]. intros r. apply getbn_set_ctx. reflexivity.
Qed.

(* [comment removed for export] *)
Definition get_leaf (ls : LS) (a : bnref * LS) : Prop :=
  fst a = RPool (cx_pused (ls_ctx ls)) /\ cx_pused (ls_ctx (snd a)) = S (cx_pused (ls_ctx ls))
  /\ cx_psize (ls_ctx (snd a)) = length (cx_vals (ls_ctx (snd a)))
  /\ (forall r, r <> RPool (cx_pused (ls_ctx ls)) -> getbn r (snd a) = getbn r ls).

Lemma BN_CTX_get_leaves : forall ls : LS, cx_psize (ls_ctx ls) = length (cx_vals (ls_ctx ls)) ->
  leaves (BN_CTX_get (tree_ops bptr) ls) (get_leaf ls).
Proof.
  intros ls Hps. unfold BN_CTX_get, bbind, bgetctx, bsetctx, bunr, bmalloc, bget, bset, bret.
  cbn [bind ret unreachable lib_malloc tree_ops tbind fst snd].
  destruct (negb (cx_err_stack (ls_ctx ls) =? 0)%nat || cx_too_many (ls_ctx ls)); [exact I|].
  set (c := ls_ctx ls) in *.
  destruct (cx_pused c =? cx_psize c)%nat eqn:EQ.
  - destruct (negb (cx_psize c =? 0)%nat) eqn:EZ; [exact I|]. set (i := cx_pused c).
    cbn [tbind leaves]. intros [p|]; [|exact I]. cbn [tbind leaves fst snd].
    apply Nat.eqb_eq in EQ. apply negb_false_iff, Nat.eqb_eq in EZ.
    assert (Ei : i = 0%nat) by (unfold i; lia).
    assert (Ev : cx_vals c = []) by (apply length_zero_iff_nil; lia).
    unfold get_leaf. cbn [fst snd set_ctx setbn ls_ctx getbn ctx_set_vals cx_vals cx_pused cx_psize]. fold c. fold i.
    rewrite Ei. split; [reflexivity|]. split; [reflexivity|].
    split. { rewrite list_set_length, repeat_length. reflexivity. }
    intros r Hr. destruct r as [| | | | |j]; try reflexivity.
    cbn [getbn set_ctx ls_ctx ctx_set_vals cx_vals]. fold c. rewrite Ev.
    rewrite nth_list_set_other by congruence.
    destruct (Nat.ltb_spec j 16) as [Hj|Hj]; [rewrite nth_repeat_lt by exact Hj | rewrite nth_overflow by (rewrite repeat_length; exact Hj)];
      destruct j; reflexivity.
  - set (i := cx_pused c). cbn [tbind leaves fst snd].
    unfold get_leaf. cbn [fst snd set_ctx setbn ls_ctx getbn ctx_set_vals cx_vals cx_pused cx_psize]. fold c. fold i.
    split; [reflexivity|]. split; [reflexivity|].
    split. { rewrite list_set_length. exact Hps. }
    intros r Hr. destruct r as [| | | | |j]; try reflexivity.
    cbn [getbn set_ctx ls_ctx ctx_set_vals cx_vals]. fold c. apply nth_list_set_other. congruence.
Qed.

(* [comment removed for export] *)
Definition same_ctr (ls ls' : LS) : Prop :=
  cx_pused (ls_ctx ls') = cx_pused (ls_ctx ls) /\ cx_psize (ls_ctx ls') = cx_psize (ls_ctx ls)
  /\ length (cx_vals (ls_ctx ls')) = length (cx_vals (ls_ctx ls)).
Lemma same_ctr_refl : forall ls, same_ctr ls ls. Proof. intros; unfold same_ctr; auto. Qed.
Lemma same_ctr_setbn : forall r b ls, same_ctr ls (setbn r b ls).
Proof. intros. unfold same_ctr. rewrite pused_setbn, psize_setbn, vals_len_setbn. auto. Qed.
Lemma same_ctr_trans : forall l1 l2 l3, same_ctr l1 l2 -> same_ctr l2 l3 -> same_ctr l1 l3.
Proof. intros l1 l2 l3 (A1 & A2 & A3) (B1 & B2 & B3). unfold same_ctr. repeat split; congruence. Qed.

(* [comment removed for export] *)
Definition wexp_leaf2 (r : bnref) (words : nat) (ls : LS) (a : unit * LS) : Prop :=
  wexp_leaf r ls a /\ (words <= bn_dmax (getbn r (snd a)))%nat /\ same_ctr ls (snd a).

Lemma bn_wexpand_leaves2 : forall r words (ls : LS), valid_refm r ls -> (bn_top (getbn r ls) <= bn_dmax (getbn r ls))%nat ->
  leaves (bn_wexpand (tree_ops bptr) r words ls) (wexp_leaf2 r words ls).
Proof.
  intros r words ls HV HT. unfold bn_wexpand, bbind, bget, bret, bunr, bmalloc, bfree_opt, bset, bfree.
  cbn [bind ret unreachable lib_malloc lib_free tree_ops tbind fst snd].
  set (b := getbn r ls) in *.
  destruct (Nat.leb_spec words (bn_dmax b)) as [LE|GT].
  { cbn [leaves]. split; [|split; [exact LE| apply same_ctr_refl]]. unfold wexp_leaf; cbn [snd]; auto. }
  destruct (BN_WORDS_MAX <? Z.of_nat words); [exact I|].
  destruct (negb (Z.land (bn_flags b) BN_FLG_STATIC_DATA =? 0)); [exact I|].
  destruct (negb (Z.land (bn_flags b) BN_FLG_SECURE =? 0)); [exact I|].
  cbn [tbind leaves]. intros [p|]; [|exact I].
  assert (NEW : wexp_leaf2 r words ls (tt, setbn r (mkBN (Some p) (firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)) (bn_top b) (bn_neg b) (bn_flags b)) ls)).
  { unfold wexp_leaf2, wexp_leaf. cbn [snd].
    rewrite getbn_setbn_same_m by exact HV. cbn [bn_top bn_neg bn_flags bn_buf]. fold b. unfold bn_dmax in *. cbn [bn_buf].
    split; [|split; [rewrite length_app, length_firstn, repeat_length; lia | apply same_ctr_setbn]].
    split; [intros r' Hne; apply getbn_setbn_other; exact Hne|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn, Nat.min_l by exact HT.
    rewrite Nat.sub_diag. cbn [firstn]. apply app_nil_r. }
  destruct (bn_d b) as [q|]; cbn [tbind leaves]; exact NEW.
Qed.

(* [comment removed for export] *)
Definition copy_leaf (ra rb : bnref) (ls : LS) (a : unit * LS) : Prop :=
  let b := getbn rb ls in
  (forall r, ra <> r -> getbn r (snd a) = getbn r ls)
  /\ bn_top (getbn ra (snd a)) = bn_top b /\ bn_neg (getbn ra (snd a)) = bn_neg b
  /\ firstn (bn_top b) (bn_buf (getbn ra (snd a))) = firstn (bn_top b) (bn_buf b)
  /\ (bn_top b <= bn_dmax (getbn ra (snd a)))%nat
  /\ same_ctr ls (snd a).

Lemma BN_copy_leaves : forall ra rb (ls : LS), ra <> rb -> valid_refm ra ls ->
  (bn_top (getbn ra ls) <= bn_dmax (getbn ra ls))%nat -> (bn_top (getbn rb ls) <= bn_dmax (getbn rb ls))%nat ->
  leaves (BN_copy (tree_ops bptr) ra rb ls) (copy_leaf ra rb ls).
Proof.
  intros ra rb ls NE HV HTa HTb. unfold BN_copy. unfold bbind at 1. unfold bget at 1. cbn [bind ret tree_ops tbind fst snd].
  set (b := getbn rb ls) in *.
  destruct (negb (Z.land (bn_flags b) BN_FLG_CONSTTIME =? 0)); [exact I|].
  replace (bnref_eqb ra rb) with false by (symmetry; destruct (bnref_eqb ra rb) eqn:E; [|reflexivity]; exfalso; apply NE;
    destruct ra, rb; cbn in E; try discriminate; try reflexivity; apply Nat.eqb_eq in E; congruence).
  unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
  apply leaves_bind'. eapply leaves_mono; [|apply (bn_wexpand_leaves2 ra (bn_top b) ls HV HTa)].
  intros [u ls1] ((W1 & W2 & W3 & W4 & W5) & WD & WC). cbn [snd fst] in *. cbn [leaves].
  unfold copy_leaf. cbn [snd]. fold b.
  assert (HV1 : valid_refm ra ls1) by (destruct ra; try exact I; cbn [valid_refm] in *; destruct WC as (_ & _ & L); rewrite L; exact HV).
  rewrite getbn_setbn_same_m by exact HV1. cbn [bn_top bn_neg bn_buf].
  split. { intros r Hr. rewrite getbn_setbn_other by exact Hr. apply W1. exact Hr. }
  split; [reflexivity|]. split; [reflexivity|].
  unfold bn_dmax in *.
  split. { destruct (Nat.ltb_spec 0 (bn_top b)) as [P|Z0].
           - apply firstn_splice_0; [rewrite length_firstn; lia | lia].
           - replace (bn_top b) with 0%nat by lia. reflexivity. }
  split. { destruct (0 <? bn_top b)%nat; [rewrite splice_length; [exact WD| rewrite length_firstn; lia] | exact WD]. }
  eapply same_ctr_trans; [exact WC| apply same_ctr_setbn].
Qed.

Lemma lshift_limbs_len : forall l lb m, length (fst (lshift_limbs l lb m)) = length l.
Proof.
  induction l as [|x l IH]; intros lb m; [reflexivity|]. cbn [lshift_limbs].
  specialize (IH lb (if lb =? 0 then 0 else shrw x (64 - lb))). destruct (lshift_limbs l lb (if lb =? 0 then 0 else shrw x (64 - lb))) as [r mo].
  cbn [fst length] in *. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Definition lsh_res (bx : bignum bptr) (n : Z) : list Z :=
  if (bn_top bx =? 0)%nat then [0] else fst (lshift_limbs (firstn (bn_top bx) (bn_buf bx)) n 0) ++ [snd (lshift_limbs (firstn (bn_top bx) (bn_buf bx)) n 0)].

Definition lsh_leaf (rr rx : bnref) (n : Z) (ls : LS) (a : unit * LS) : Prop :=
  let bx := getbn rx ls in
  (forall r, rr <> r -> getbn r (snd a) = getbn r ls)
  /\ bn_top (getbn rr (snd a)) = (bn_top bx + 1)%nat /\ bn_neg (getbn rr (snd a)) = bn_neg bx
  /\ firstn (bn_top bx + 1) (bn_buf (getbn rr (snd a))) = lsh_res bx n
  /\ (bn_top bx + 1 <= bn_dmax (getbn rr (snd a)))%nat
  /\ same_ctr ls (snd a).

Lemma bn_lshift_leaves : forall rr rx n (ls : LS), rr <> rx -> 0 <= n < 64 -> valid_refm rr ls ->
  (bn_top (getbn rr ls) <= bn_dmax (getbn rr ls))%nat -> (bn_top (getbn rx ls) <= bn_dmax (getbn rx ls))%nat ->
  leaves (bn_lshift_fixed_top (tree_ops bptr) rr rx n ls) (lsh_leaf rr rx n ls).
Proof.
  intros rr rx n ls NE Hn HV HTr HTx. unfold bn_lshift_fixed_top.
  replace (bnref_eqb rr rx) with false by (symmetry; destruct (bnref_eqb rr rx) eqn:E; [|reflexivity]; exfalso; apply NE;
    destruct rr, rx; cbn in E; try discriminate; try reflexivity; apply Nat.eqb_eq in E; congruence).
  replace (n <? 64) with true by (symmetry; apply Z.ltb_lt; lia). cbn [orb negb].
  unfold bbind, bget, bset. cbn [bind ret tree_ops tbind fst snd].
  set (bx := getbn rx ls) in *.
  apply leaves_bind'. eapply leaves_mono; [|apply (bn_wexpand_leaves2 rr (bn_top bx + 1) ls HV HTr)].
  intros [u ls1] ((W1 & W2 & W3 & W4 & W5) & WD & WC). cbn [snd fst] in *. cbn [leaves].
  unfold lsh_leaf. cbn [snd]. fold bx.
  assert (HV1 : valid_refm rr ls1) by (destruct rr; try exact I; cbn [valid_refm] in *; destruct WC as (_ & _ & L); rewrite L; exact HV).
  rewrite getbn_setbn_same_m by exact HV1. cbn [bn_top bn_neg bn_buf].
  split. { intros r Hr. rewrite getbn_setbn_other by exact Hr. apply W1. exact Hr. }
  split; [reflexivity|]. split; [reflexivity|].
  unfold bn_dmax, lsh_res in *.
  destruct (Nat.eqb_spec (bn_top bx) 0) as [Z0|NZ].
  - rewrite Z0 in *. cbn [Nat.add].
    split. { unfold upd. apply (firstn_splice_0 (bn_buf (getbn rr ls1)) [0] 1); [reflexivity | lia]. }
    split; [rewrite upd_length by lia; exact WD| eapply same_ctr_trans; [exact WC| apply same_ctr_setbn]].
  - pose proof (lshift_limbs_len (firstn (bn_top bx) (bn_buf bx)) n 0) as L0.
    destruct (lshift_limbs (firstn (bn_top bx) (bn_buf bx)) n 0) as [l0 mo]. cbn [fst snd] in *.
    assert (LL : length (l0 ++ [mo]) = (bn_top bx + 1)%nat) by (rewrite length_app, L0, length_firstn; cbn [length]; lia).
    split. { apply firstn_splice_0; [exact LL | lia]. }
    split; [rewrite splice_length by lia; exact WD | eapply same_ctr_trans; [exact WC| apply same_ctr_setbn]].
Qed.
