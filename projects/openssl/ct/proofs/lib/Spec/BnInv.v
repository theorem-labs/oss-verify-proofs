(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Inv.
Context {ptr : Type}.
Local Notation LS := (lstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition DMAX_MAX : Z := 65536.     (* [comment removed for export] *)

Definition bn_ok (b : BN) : Prop :=
  limbs (bn_buf b) /\ (bn_top b <= bn_dmax b)%nat /\ Z.of_nat (bn_dmax b) <= DMAX_MAX /\ (bn_flags b = 0 \/ bn_flags b = 1).

Definition pool_ok (vals : list BN) : Prop :=
  vals = [] \/ exists p0 p1 p2, vals = p0 :: p1 :: p2 :: repeat (bn_nil 0) 13 /\ bn_ok p0 /\ bn_ok p1 /\ bn_ok p2.

Definition st_ok (s : LS) : Prop :=
  bn_ok (ls_b1 s) /\ bn_ok (ls_b2 s) /\ bn_ok (ls_b3 s) /\ bn_ok (ls_b4 s) /\ bn_ok (ls_b5 s) /\
  pool_ok (cx_vals (ls_ctx s)).

Definition bn_blocks (b : BN) : blocks :=
  match bn_d b with Some p => [(p, 8 * Z.of_nat (bn_dmax b))] | None => [] end.

Definition opt_block (p : option ptr) (n : Z) : blocks := match p with Some q => [(q, n)] | None => [] end.

Definition blocks_of (s : LS) : blocks :=
  bn_blocks (ls_b1 s) ++ bn_blocks (ls_b2 s) ++ bn_blocks (ls_b3 s) ++ bn_blocks (ls_b4 s) ++ bn_blocks (ls_b5 s) ++
  concat (map bn_blocks (cx_vals (ls_ctx s))) ++
  opt_block (cx_head (ls_ctx s)) POOL_ITEM_BYTES ++ opt_block (cx_indexes (ls_ctx s)) (4 * Z.of_nat BN_CTX_START_FRAMES).

Definition own (s : LS) (X : blocks) : Prop := Permutation X (blocks_of s).

Definition valid_ref (r : bnref) (s : LS) : Prop :=
  match r with RPool i => (i < 3)%nat /\ cx_vals (ls_ctx s) <> [] | _ => True end.

Lemma bn_ok_nil : forall f, f = 0 \/ f = 1 -> bn_ok (bn_nil f).
Proof. intros f Hf. unfold bn_ok, bn_nil, bn_dmax, DMAX_MAX. cbn. split; [constructor|]. split; [lia|]. split; [lia|exact Hf]. Qed.

Lemma bn_blocks_length : forall b, (length (bn_blocks b) <= 1)%nat.
Proof. intros b. unfold bn_blocks. destruct (bn_d b); cbn; lia. Qed.

Lemma bn_blocks_size : forall b, bn_ok b -> Forall (fun xb : ptr * Z => 0 <= snd xb <= BSZ) (bn_blocks b).
Proof.
  intros b (_ & _ & Hd & _). unfold bn_blocks. destruct (bn_d b); constructor; [|constructor].
  cbn [snd]. unfold BSZ, DMAX_MAX in *. lia.
Qed.

Lemma bn_blocks_nil : forall f, bn_blocks (bn_nil f : BN) = [].
Proof. reflexivity. Qed.

Lemma concat_nil_blocks : forall n, concat (map bn_blocks (repeat (bn_nil 0 : BN) n)) = [].
Proof. induction n as [|n IH]; cbn [repeat map concat]; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma st_ok_blocks : forall s, st_ok s ->
  (length (blocks_of s) <= 10)%nat /\ Forall (fun xb => 0 <= snd xb <= BSZ) (blocks_of s).
Proof.
  intros s (H1 & H2 & H3 & H4 & H5 & Hp). unfold blocks_of.
  assert (Hpool : (length (concat (map bn_blocks (cx_vals (ls_ctx s)))) <= 3)%nat /\
                  Forall (fun xb => 0 <= snd xb <= BSZ) (concat (map bn_blocks (cx_vals (ls_ctx s))))).
  { destruct Hp as [E|(p0 & p1 & p2 & E & Hp0 & Hp1 & Hp2)]; rewrite E.
    - cbn. split; [lia|constructor].
    - cbn [map concat]. rewrite concat_nil_blocks, app_nil_r. rewrite !length_app.
      pose proof (bn_blocks_length p0). pose proof (bn_blocks_length p1). pose proof (bn_blocks_length p2).
      split; [lia|]. rewrite !Forall_app. repeat split; apply bn_blocks_size; assumption. }
  destruct Hpool as [Hpl Hps]. rewrite !length_app.
  pose proof (bn_blocks_length (ls_b1 s)). pose proof (bn_blocks_length (ls_b2 s)). pose proof (bn_blocks_length (ls_b3 s)).
  pose proof (bn_blocks_length (ls_b4 s)). pose proof (bn_blocks_length (ls_b5 s)).
  assert (Ho1 : (length (opt_block (cx_head (ls_ctx s)) POOL_ITEM_BYTES) <= 1)%nat) by (destruct (cx_head (ls_ctx s)); cbn; lia).
  assert (Ho2 : (length (opt_block (cx_indexes (ls_ctx s)) (4 * Z.of_nat BN_CTX_START_FRAMES)) <= 1)%nat)
    by (destruct (cx_indexes (ls_ctx s)); cbn; lia).
  split; [lia|].
  rewrite !Forall_app. repeat split; try (apply bn_blocks_size; assumption); try exact Hps.
  - destruct (cx_head (ls_ctx s)); constructor; [|constructor]. cbn [snd]. unfold BSZ, POOL_ITEM_BYTES. lia.
  - destruct (cx_indexes (ls_ctx s)); constructor; [|constructor]. cbn [snd]. unfold BSZ, BN_CTX_START_FRAMES. lia.
Qed.

Lemma own_ok_bn : forall s X n, st_ok s -> own s X -> 0 <= n <= BSZ -> ok_bn X n.
Proof.
  intros s X n Hs Ho Hn. destruct (st_ok_blocks s Hs) as [Hl Hf]. unfold ok_bn, NBLK.
  split; [rewrite (Permutation_length Ho); lia|]. split; [exact Hn|].
  eapply Permutation_Forall; [apply Permutation_sym; exact Ho|exact Hf].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bwp {A} (m : BM (M:=btree ptr) (ptr:=ptr) A) (s : LS) (X : blocks) (Q : A -> LS -> blocks -> Prop) : Prop :=
  wp (m s) X (fun p X' => Q (fst p) (snd p) X').

Lemma bwp_ret : forall {A} (a : A) s X Q, Q a s X -> bwp (bret ops a) s X Q.
Proof. intros. exact H. Qed.

Lemma bwp_bind : forall {A B} (m : BM A) (f : A -> BM B) s X Q,
  bwp m s X (fun a s' X' => bwp (f a) s' X' Q) -> bwp (bbind ops m f) s X Q.
Proof. intros A B m f s X Q H. unfold bwp, bbind. cbn [bind tree_ops]. apply wp_bind. exact H. Qed.

Lemma bwp_mono : forall {A} (m : BM A) s X (Q Q' : A -> LS -> blocks -> Prop),
  bwp m s X Q -> (forall a s' X', Q a s' X' -> Q' a s' X') -> bwp m s X Q'.
Proof. intros A m s X Q Q' H HQ. unfold bwp in *. eapply wp_mono; [exact H|]. intros [a s'] X'. cbn. apply HQ. Qed.

Lemma bwp_get : forall r s X Q, Q (getbn r s) s X -> bwp (bget ops r) s X Q.
Proof. intros. exact H. Qed.
Lemma bwp_set : forall r b s X Q, Q tt (setbn r b s) X -> bwp (bset ops r b) s X Q.
Proof. intros. exact H. Qed.
Lemma bwp_getctx : forall s X Q, Q (ls_ctx s) s X -> bwp (bgetctx ops) s X Q.
Proof. intros. exact H. Qed.
Lemma bwp_setctx : forall c s X Q, Q tt (set_ctx c s) X -> bwp (bsetctx ops c) s X Q.
Proof. intros. exact H. Qed.

Lemma bwp_malloc : forall n s X Q, ok_bn X n -> (forall p, ~ In p (map fst X) -> Q p s ((p, n) :: X)) ->
  bwp (bmalloc ops n) s X Q.
Proof.
  intros n s X Q Hok HQ. unfold bwp, bmalloc. cbn [bind lib_malloc tree_ops tbind wp ret unreachable].
  split; [exact Hok|]. split; [reflexivity|]. intros p Hp. cbn [wp fst snd]. apply HQ. exact Hp.
Qed.

Lemma bwp_free_opt : forall p n s X X0 Q, Permutation X (opt_block p n ++ X0) ->
  (forall X', Permutation X' X0 -> Q tt s X') -> bwp (bfree_opt ops p) s X Q.
Proof.
  intros [q|] n s X X0 Q HP HQ; unfold bwp, bfree_opt, bfree, bret; cbn [bind lib_free tree_ops tbind wp ret fst snd opt_block app] in *.
  - exists n, X0. split; [exact HP|]. apply HQ. apply Permutation_refl.
  - apply HQ. exact HP.
Qed.

Lemma bwp_unr_false : forall {A} s X (Q : A -> LS -> blocks -> Prop), bwp (bunr ops) s X Q -> False.
Proof. intros A s X Q H. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma st_ok_pool : forall s, st_ok s -> cx_vals (ls_ctx s) <> [] ->
  exists p0 p1 p2, cx_vals (ls_ctx s) = p0 :: p1 :: p2 :: repeat (bn_nil 0) 13 /\ bn_ok p0 /\ bn_ok p1 /\ bn_ok p2.
Proof. intros s (_ & _ & _ & _ & _ & [E|H]) Hne; [contradiction|exact H]. Qed.

Lemma getbn_setbn_same : forall r b s, st_ok s -> valid_ref r s -> getbn r (setbn r b s) = b.
Proof.
  intros r b s Hs Hv. destruct r as [| | | | |i]; try reflexivity.
  destruct Hv as [Hi Hne]. destruct (st_ok_pool s Hs Hne) as (p0 & p1 & p2 & E & _).
  cbn [getbn setbn set_ctx ls_ctx ctx_set_vals cx_vals]. rewrite E.
  assert (i = 0 \/ i = 1 \/ i = 2)%nat as [->|[->| ->]] by lia; reflexivity.
Qed.

Lemma setbn_getbn_id : forall r s, st_ok s -> valid_ref r s -> setbn r (getbn r s) s = s.
Proof.
  intros r s Hs Hv. destruct s as [b1 b2 b3 b4 b5 c]. destruct r as [| | | | |i]; try reflexivity.
  destruct Hv as [Hi Hne]. destruct (st_ok_pool _ Hs Hne) as (p0 & p1 & p2 & E & _).
  destruct c as [hd cur vals pu ps idx fr ss us es tm]. cbn [ls_ctx cx_vals] in E. subst vals.
  assert (i = 0 \/ i = 1 \/ i = 2)%nat as [->|[->| ->]] by lia; reflexivity.
Qed.

Lemma st_ok_setbn : forall r b s, st_ok s -> valid_ref r s -> bn_ok b -> st_ok (setbn r b s).
Proof.
  intros r b s Hs Hv Hb. pose proof Hs as (H1 & H2 & H3 & H4 & H5 & Hp).
  destruct r as [| | | | |i]; try (unfold st_ok; cbn [setbn ls_b1 ls_b2 ls_b3 ls_b4 ls_b5 ls_ctx]; tauto).
  destruct Hv as [Hi Hne]. destruct (st_ok_pool s Hs Hne) as (p0 & p1 & p2 & E & Hp0 & Hp1 & Hp2).
  unfold st_ok. cbn [setbn set_ctx ls_b1 ls_b2 ls_b3 ls_b4 ls_b5 ls_ctx ctx_set_vals cx_vals]. rewrite E.
  repeat (split; [assumption|]). right.
  assert (i = 0 \/ i = 1 \/ i = 2)%nat as [->|[->| ->]] by lia; cbn [list_set].
  - exists b, p1, p2. tauto.
  - exists p0, b, p2. tauto.
  - exists p0, p1, b. tauto.
Qed.

(* [comment removed for export] *)
Lemma perm_pick : forall (L1 M L2 W : list (ptr * Z)), W = L1 ++ M ++ L2 -> Permutation W (M ++ L1 ++ L2).
Proof. intros L1 M L2 W ->. apply Permutation_app_swap_app. Qed.

Lemma blocks_setbn : forall r s, st_ok s -> valid_ref r s ->
  exists R, Permutation (blocks_of s) (bn_blocks (getbn r s) ++ R) /\
            forall b, Permutation (blocks_of (setbn r b s)) (bn_blocks b ++ R).
Proof.
  intros r s Hs Hv. destruct s as [b1 b2 b3 b4 b5 c].
  set (P := concat (map bn_blocks (cx_vals c))).
  set (T := opt_block (cx_head c) POOL_ITEM_BYTES ++ opt_block (cx_indexes c) (4 * Z.of_nat BN_CTX_START_FRAMES)).
  destruct r as [| | | | |i]; unfold blocks_of; cbn [getbn setbn ls_b1 ls_b2 ls_b3 ls_b4 ls_b5 ls_ctx]; fold P T.
  - exists ([] ++ bn_blocks b2 ++ bn_blocks b3 ++ bn_blocks b4 ++ bn_blocks b5 ++ P ++ T).
    split; [|intros b]; apply perm_pick; reflexivity.
  - exists (bn_blocks b1 ++ bn_blocks b3 ++ bn_blocks b4 ++ bn_blocks b5 ++ P ++ T).
    split; [|intros b]; apply perm_pick; reflexivity.
  - exists ((bn_blocks b1 ++ bn_blocks b2) ++ bn_blocks b4 ++ bn_blocks b5 ++ P ++ T).
    split; [|intros b]; apply perm_pick; rewrite <- !app_assoc; reflexivity.
  - exists ((bn_blocks b1 ++ bn_blocks b2 ++ bn_blocks b3) ++ bn_blocks b5 ++ P ++ T).
    split; [|intros b]; apply perm_pick; rewrite <- !app_assoc; reflexivity.
  - exists ((bn_blocks b1 ++ bn_blocks b2 ++ bn_blocks b3 ++ bn_blocks b4) ++ P ++ T).
    split; [|intros b]; apply perm_pick; rewrite <- !app_assoc; reflexivity.
  - destruct Hv as [Hi Hne]. destruct (st_ok_pool _ Hs Hne) as (p0 & p1 & p2 & E & _).
    destruct c as [hd cur vals pu ps idx fr ss us es tm]. cbn [ls_ctx cx_vals cx_head cx_indexes set_ctx ctx_set_vals] in *. subst vals.
    subst P. set (Bs := bn_blocks b1 ++ bn_blocks b2 ++ bn_blocks b3 ++ bn_blocks b4 ++ bn_blocks b5).
    assert (i = 0 \/ i = 1 \/ i = 2)%nat as [->|[->| ->]] by lia; cbn [list_set nth map concat]; rewrite concat_nil_blocks, app_nil_r.
    + exists (Bs ++ bn_blocks p1 ++ bn_blocks p2 ++ T).
      split; [|intros b]; apply perm_pick; subst Bs; rewrite <- !app_assoc; reflexivity.
    + exists ((Bs ++ bn_blocks p0) ++ bn_blocks p2 ++ T).
      split; [|intros b]; apply perm_pick; subst Bs; rewrite <- !app_assoc; reflexivity.
    + exists ((Bs ++ bn_blocks p0 ++ bn_blocks p1) ++ T).
      split; [|intros b]; apply perm_pick; subst Bs; rewrite <- !app_assoc; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition expanded (b : BN) (words : nat) (b' : BN) : Prop :=
  bn_top b' = bn_top b /\ bn_neg b' = bn_neg b /\ bn_flags b' = bn_flags b /\
  bn_buf b' = (if (words <=? bn_dmax b)%nat then bn_buf b
               else firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)) /\
  bn_ok b' /\ (words <= bn_dmax b')%nat /\ (bn_dmax b <= bn_dmax b')%nat.

Lemma bn_wexpand_spec : forall r words s X (Q : unit -> LS -> blocks -> Prop),
  st_ok s -> own s X -> valid_ref r s -> bn_ok (getbn r s) -> Z.of_nat words <= DMAX_MAX ->
  (forall b' X', expanded (getbn r s) words b' -> st_ok (setbn r b' s) -> own (setbn r b' s) X' ->
                 Q tt (setbn r b' s) X') ->
  bwp (bn_wexpand ops r words) s X Q.
Proof.
  intros r words s X Q Hs Ho Hv Hb Hw HQ. unfold bn_wexpand.
  apply bwp_bind, bwp_get. set (b := getbn r s) in *.
  destruct Hb as (Hb1 & Hb2 & Hb3 & Hb4).
  destruct (Nat.leb_spec words (bn_dmax b)) as [Hle|Hgt].
  - apply bwp_ret. rewrite <- (setbn_getbn_id r s Hs Hv). fold b. apply HQ.
    + unfold expanded. destruct (Nat.leb_spec words (bn_dmax b)); [|lia].
      repeat split; try reflexivity; try assumption; lia.
    + unfold b. rewrite setbn_getbn_id by assumption. exact Hs.
    + unfold b. rewrite setbn_getbn_id by assumption. exact Ho.
  - destruct (Z.ltb_spec BN_WORDS_MAX (Z.of_nat words)) as [Hbig|_]; [unfold BN_WORDS_MAX, DMAX_MAX in *; lia|].
    assert (Ef1 : (Z.land (bn_flags b) BN_FLG_STATIC_DATA =? 0) = true) by (destruct Hb4 as [-> | ->]; reflexivity).
    assert (Ef2 : (Z.land (bn_flags b) BN_FLG_SECURE =? 0) = true) by (destruct Hb4 as [-> | ->]; reflexivity).
    rewrite Ef1, Ef2. cbn [negb].
    destruct (blocks_setbn r s Hs Hv) as (R & HR1 & HR2). fold b in HR1.
    apply bwp_bind, bwp_malloc.
    { eapply own_ok_bn; [exact Hs|exact Ho|]. unfold BSZ, DMAX_MAX in *. lia. }
    intros p Hp. apply bwp_bind.
    apply (bwp_free_opt (bn_d b) (8 * Z.of_nat (bn_dmax b)) s _ ((p, 8 * Z.of_nat words) :: R)).
    { unfold own in Ho. apply Permutation_trans with ((p, 8 * Z.of_nat words) :: bn_blocks b ++ R).
      - apply perm_skip. apply Permutation_trans with (blocks_of s); assumption.
      - unfold bn_blocks. apply Permutation_middle. }
    intros X' HX'. apply bwp_set.
    set (b' := mkBN (Some p) (firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)) (bn_top b) (bn_neg b) (bn_flags b)).
    assert (Hlen : length (firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)) = words).
    { rewrite length_app, firstn_length_le, repeat_length by exact Hb2. unfold bn_dmax in *. lia. }
    assert (Hb' : bn_ok b').
    { unfold bn_ok, bn_dmax. subst b'. cbn [bn_buf bn_top bn_flags]. rewrite Hlen.
      split; [apply limbs_app; [apply limbs_firstn; exact Hb1|apply limbs_repeat; exact limb_0]|].
      split; [unfold bn_dmax in *; lia|]. split; [exact Hw|exact Hb4]. }
    apply HQ.
    + unfold expanded. destruct (Nat.leb_spec words (bn_dmax b)); [lia|].
      assert (Hd' : bn_dmax b' = words) by (unfold bn_dmax; subst b'; cbn [bn_buf]; exact Hlen).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact Hb'|]. rewrite Hd'. lia.
    + apply st_ok_setbn; assumption.
    + unfold own. apply Permutation_trans with ((p, 8 * Z.of_nat words) :: R); [exact HX'|].
      apply Permutation_sym. specialize (HR2 b'). unfold bn_blocks at 1 in HR2. subst b'. cbn [bn_d] in HR2.
      unfold bn_dmax in HR2. cbn [bn_buf] in HR2. rewrite Hlen in HR2. exact HR2.
Qed.

End Inv.
