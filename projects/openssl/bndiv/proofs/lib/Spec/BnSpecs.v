(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords BnInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Specs.
Context {ptr : Type}.
Local Notation LS := (lstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bn_mag (b : BN) : Z := lval (firstn (bn_top b) (bn_buf b)).
Definition bn_norm (b : BN) : Prop := bn_top b = 0%nat \/ nth (bn_top b - 1) (bn_buf b) 0 <> 0.
Definition bn_canon (b : BN) : Prop := bn_norm b /\ (bn_top b = 0%nat -> bn_neg b = false).
Definition bn_val (b : BN) : Z := if bn_neg b then - bn_mag b else bn_mag b.

Lemma bn_mag_top0 : forall b : BN, bn_top b = 0%nat -> bn_mag b = 0.
Proof. intros b E. unfold bn_mag. rewrite E. reflexivity. Qed.

Lemma bn_mag_nonneg : forall b, bn_ok b -> 0 <= bn_mag b.
Proof. intros b (H & _). apply lval_nonneg, limbs_firstn. exact H. Qed.

Lemma bn_mag_lt : forall b, bn_ok b -> bn_mag b < Bp (bn_top b).
Proof.
  intros b (H & Ht & _). unfold bn_mag. pose proof (lval_bound _ (limbs_firstn (bn_top b) _ H)) as Hb.
  rewrite firstn_length_le in Hb by exact Ht. lia.
Qed.

(* [comment removed for export] *)
Lemma bn_mag_ge : forall b, bn_ok b -> bn_norm b -> (0 < bn_top b)%nat -> Bp (bn_top b - 1) <= bn_mag b.
Proof.
  intros b (H & Ht & _) [Hn|Hn] Hpos; [lia|]. unfold bn_mag.
  set (l := firstn (bn_top b) (bn_buf b)).
  assert (Hl : limbs l) by (apply limbs_firstn; exact H).
  assert (Hll : length l = bn_top b) by (apply firstn_length_le; exact Ht).
  pose proof (nth_limb_val l (bn_top b - 1) Hl ltac:(lia)) as E.
  assert (En : nth (bn_top b - 1) l 0 = nth (bn_top b - 1) (bn_buf b) 0).
  { subst l. rewrite nth_firstn. destruct (Nat.ltb_spec (bn_top b - 1) (bn_top b)); [reflexivity|lia]. }
  rewrite En in E. pose proof (limbs_nth (bn_buf b) (bn_top b - 1) H) as [Hx0 _].
  pose proof (lval_nonneg _ (limbs_firstn (bn_top b - 1) l Hl)). pose proof (lval_nonneg _ (limbs_skipn (S (bn_top b - 1)) l Hl)).
  pose proof (Bp_pos (bn_top b - 1)). pose proof (Bp_pos (S (bn_top b - 1))). nia.
Qed.

Lemma bn_norm_zero_iff : forall b, bn_ok b -> bn_norm b -> (bn_top b = 0%nat <-> bn_mag b = 0).
Proof.
  intros b Hb Hn. split.
  - intros E. unfold bn_mag. rewrite E. reflexivity.
  - intros E. destruct (Nat.eq_dec (bn_top b) 0) as [|Hne]; [assumption|exfalso].
    pose proof (bn_mag_ge b Hb Hn ltac:(lia)). pose proof (Bp_pos (bn_top b - 1)). lia.
Qed.

(* [comment removed for export] *)
Lemma bn_norm_mag_inj : forall a b, bn_ok a -> bn_ok b -> bn_norm a -> bn_norm b -> bn_mag a = bn_mag b ->
  bn_top a = bn_top b /\ firstn (bn_top a) (bn_buf a) = firstn (bn_top b) (bn_buf b).
Proof.
  intros a b Ha Hb Hna Hnb E.
  assert (Ht : bn_top a = bn_top b).
  { destruct (Nat.lt_trichotomy (bn_top a) (bn_top b)) as [Hlt|[Heq|Hgt]]; [exfalso|exact Heq|exfalso].
    - pose proof (bn_mag_lt a Ha). pose proof (bn_mag_ge b Hb Hnb ltac:(lia)).
      pose proof (Bp_mono (bn_top a) (bn_top b - 1) ltac:(lia)). lia.
    - pose proof (bn_mag_lt b Hb). pose proof (bn_mag_ge a Ha Hna ltac:(lia)).
      pose proof (Bp_mono (bn_top b) (bn_top a - 1) ltac:(lia)). lia. }
  split; [exact Ht|]. destruct Ha as (Ha1 & Ha2 & _). destruct Hb as (Hb1 & Hb2 & _).
  apply lval_inj; [apply limbs_firstn; assumption|apply limbs_firstn; assumption| |exact E].
  unfold bn_dmax in *. rewrite !firstn_length_le by lia. exact Ht.
Qed.

(* [comment removed for export] *)
Lemma bn_correct_top_ok : forall b, bn_ok b ->
  let b' := bn_correct_top_pure b in
  bn_ok b' /\ bn_canon b' /\ bn_mag b' = bn_mag b /\ (bn_top b' <= bn_top b)%nat /\
  bn_buf b' = bn_buf b /\ bn_d b' = bn_d b /\ bn_flags b' = bn_flags b /\
  bn_neg b' = (bn_neg b && negb (bn_top b' =? 0)%nat).
Proof.
  intros b (H1 & H2 & H3 & H4). cbv zeta. unfold bn_correct_top_pure.
  destruct (strip_top_spec (bn_buf b) (bn_top b) H2) as (S1 & S2 & S3).
  set (t := strip_top (bn_buf b) (bn_top b)) in *.
  unfold bn_ok, bn_canon, bn_norm, bn_mag, bn_dmax. cbn [bn_buf bn_top bn_neg bn_flags bn_d].
  repeat split; try assumption; try lia.
  - unfold bn_dmax in *. lia.
  - intros E. rewrite E. reflexivity.
  - destruct (Nat.eqb_spec t 0); cbn [negb]; [rewrite andb_false_r|rewrite andb_true_r]; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma list_set_list_set : forall {A} (l : list A) i a b, list_set (list_set l i a) i b = list_set l i b.
Proof. induction l as [|x l IH]; intros [|i] a b; cbn [list_set]; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma nth_list_set_other : forall {A} (l : list A) i j a d, i <> j -> nth j (list_set l i a) d = nth j l d.
Proof.
  induction l as [|x l IH]; intros [|i] [|j] a d H; cbn [list_set nth]; try reflexivity; try lia.
  apply IH. lia.
Qed.

Lemma list_set_nil_iff : forall {A} (l : list A) i a, list_set l i a = [] <-> l = [].
Proof. intros A [|x l] [|i] a; cbn [list_set]; split; intros H; try reflexivity; try discriminate. Qed.

Lemma setbn_setbn_same : forall r b1 b2 (s : LS), setbn r b2 (setbn r b1 s) = setbn r b2 s.
Proof.
  intros r b1 b2 s. destruct r as [| | | | |i]; try reflexivity.
  cbn [setbn set_ctx ls_ctx ctx_set_vals cx_vals ls_b1 ls_b2 ls_b3 ls_b4 ls_b5 cx_head cx_current cx_pused cx_psize
       cx_indexes cx_frames cx_ssize cx_used cx_err_stack cx_too_many].
  rewrite list_set_list_set. reflexivity.
Qed.

Lemma getbn_setbn_other : forall r r' b (s : LS), r <> r' -> getbn r' (setbn r b s) = getbn r' s.
Proof.
  intros r r' b s Hne. destruct r as [| | | | |i]; destruct r' as [| | | | |j]; try reflexivity; try congruence.
  cbn [getbn setbn set_ctx ls_ctx ctx_set_vals cx_vals]. apply nth_list_set_other. congruence.
Qed.

Lemma valid_ref_setbn : forall r r' b (s : LS), valid_ref r' s -> valid_ref r' (setbn r b s).
Proof.
  intros r r' b s Hv. destruct r' as [| | | | |j]; try exact I. destruct Hv as [Hj Hne]. split; [exact Hj|].
  destruct r as [| | | | |i]; try exact Hne.
  cbn [setbn set_ctx ls_ctx ctx_set_vals cx_vals]. intros E. apply list_set_nil_iff in E. contradiction.
Qed.

(* [comment removed for export] *)
Definition ctx_same (c c' : bn_ctx ptr) : Prop :=
  cx_head c' = cx_head c /\ cx_current c' = cx_current c /\ cx_pused c' = cx_pused c /\ cx_psize c' = cx_psize c /\
  cx_indexes c' = cx_indexes c /\ cx_frames c' = cx_frames c /\ cx_ssize c' = cx_ssize c /\ cx_used c' = cx_used c /\
  cx_err_stack c' = cx_err_stack c /\ cx_too_many c' = cx_too_many c /\ (cx_vals c' = [] <-> cx_vals c = []).

Lemma ctx_same_refl : forall c, ctx_same c c.
Proof. intros c. unfold ctx_same. tauto. Qed.

Lemma ctx_same_trans : forall c1 c2 c3, ctx_same c1 c2 -> ctx_same c2 c3 -> ctx_same c1 c3.
Proof.
  intros c1 c2 c3 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11).
  unfold ctx_same. repeat split; try congruence; tauto.
Qed.

Lemma ctx_same_setbn : forall r b (s : LS), ctx_same (ls_ctx s) (ls_ctx (setbn r b s)).
Proof.
  intros r b s. destruct r as [| | | | |i]; try apply ctx_same_refl.
  unfold ctx_same. cbn [setbn set_ctx ls_ctx ctx_set_vals cx_vals cx_head cx_current cx_pused cx_psize
       cx_indexes cx_frames cx_ssize cx_used cx_err_stack cx_too_many].
  repeat split; try reflexivity; apply list_set_nil_iff.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ctx_wf (c : bn_ctx ptr) : Prop :=
  cx_err_stack c = 0%nat /\ cx_too_many c = false /\ cx_pused c = cx_used c /\ (cx_used c <= 3)%nat /\
  ((cx_psize c = 0%nat /\ cx_vals c = [] /\ cx_head c = None /\ cx_used c = 0%nat) \/ (cx_psize c = 16%nat /\ cx_vals c <> [])) /\
  ((cx_ssize c = 0%nat /\ cx_frames c = [] /\ cx_indexes c = None) \/ cx_ssize c = 32%nat) /\
  (cx_frames c = [] \/ cx_frames c = [0%nat]) /\ (cx_frames c = [] -> cx_used c = 0%nat).

(* [comment removed for export] *)
Definition ctx_rest (c : bn_ctx ptr) : Prop := ctx_wf c /\ cx_frames c = [].

Lemma ctx_wf_same : forall c c', ctx_same c c' -> ctx_wf c -> ctx_wf c'.
Proof.
  intros c c' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11) (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
  unfold ctx_wf. rewrite A1, A3, A4, A5, A6, A7, A8, A9, A10.
  repeat split; try assumption.
  destruct W5 as [(P1 & P2 & P3 & P4)|(P1 & P2)]; [left|right]; repeat split; try assumption; tauto.
Qed.

Lemma st_ok_set_ctx : forall c (s : LS), st_ok s -> pool_ok (cx_vals c) -> st_ok (set_ctx c s).
Proof. intros c s (H1 & H2 & H3 & H4 & H5 & _) Hp. unfold st_ok. cbn [set_ctx ls_b1 ls_b2 ls_b3 ls_b4 ls_b5 ls_ctx]. tauto. Qed.

Lemma getbn_set_ctx : forall r c (s : LS), cx_vals c = cx_vals (ls_ctx s) -> getbn r (set_ctx c s) = getbn r s.
Proof. intros r c s E. destruct r; try reflexivity. cbn [getbn set_ctx ls_ctx]. rewrite E. reflexivity. Qed.

Lemma BN_CTX_start_spec : forall s X (Q : unit -> LS -> blocks -> Prop),
  st_ok s -> own s X -> ctx_rest (ls_ctx s) ->
  (forall s' X', (forall r, getbn r s' = getbn r s) -> st_ok s' -> own s' X' -> ctx_wf (ls_ctx s') ->
                 cx_frames (ls_ctx s') = [0%nat] -> cx_used (ls_ctx s') = 0%nat -> Q tt s' X') ->
  bwp (BN_CTX_start ops) s X Q.
Proof.
  intros s X Q Hs Ho [(W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8) Hfr] HQ. unfold BN_CTX_start.
  apply bwp_bind, bwp_getctx. set (c := ls_ctx s) in *.
  rewrite W1, W2. cbn [Nat.eqb negb orb]. rewrite Hfr. cbn [length app].
  specialize (W8 Hfr).
  destruct W6 as [(S1 & S2 & S3)|S1].
  - (* [comment removed for export] *)
    rewrite S1. cbn [Nat.eqb negb]. apply bwp_bind, bwp_malloc.
    { eapply own_ok_bn; [exact Hs|exact Ho|]. unfold BSZ, BN_CTX_START_FRAMES. lia. }
    intros p Hp. apply bwp_bind. rewrite S3.
    apply (bwp_free_opt None 0 s _ ((p, 4 * Z.of_nat BN_CTX_START_FRAMES) :: X)); [apply Permutation_refl|].
    intros X' HX'. apply bwp_setctx. apply HQ.
    + intros r. apply getbn_set_ctx. reflexivity.
    + apply st_ok_set_ctx; [exact Hs|]. destruct Hs as (_ & _ & _ & _ & _ & Hp'). exact Hp'.
    + unfold own in *. unfold blocks_of. cbn [set_ctx ls_b1 ls_b2 ls_b3 ls_b4 ls_b5 ls_ctx cx_vals cx_head cx_indexes opt_block].
      fold c. eapply Permutation_trans; [exact HX'|].
      unfold blocks_of in Ho. fold c in Ho. rewrite S3 in Ho. cbn [opt_block] in Ho. rewrite app_nil_r in Ho.
      rewrite !app_assoc. apply Permutation_cons_app. rewrite app_nil_r. rewrite <- !app_assoc. exact Ho.
    + unfold ctx_wf. cbn [set_ctx ls_ctx cx_err_stack cx_too_many cx_pused cx_used cx_psize cx_vals cx_head cx_ssize cx_frames cx_indexes].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
      split; [right; reflexivity|]. split; [right; rewrite W8; reflexivity|]. intros E; discriminate.
    + cbn [set_ctx ls_ctx cx_frames]. rewrite W8. reflexivity.
    + cbn [set_ctx ls_ctx cx_used]. exact W8.
  - rewrite S1. cbn [Nat.eqb]. apply bwp_setctx. apply HQ.
    + intros r. apply getbn_set_ctx. reflexivity.
    + apply st_ok_set_ctx; [exact Hs|]. destruct Hs as (_ & _ & _ & _ & _ & Hp'). exact Hp'.
    + exact Ho.
    + unfold ctx_wf. cbn [set_ctx ls_ctx cx_err_stack cx_too_many cx_pused cx_used cx_psize cx_vals cx_head cx_ssize cx_frames cx_indexes].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
      split; [right; reflexivity|]. split; [right; rewrite W8; reflexivity|]. intros E; discriminate.
    + cbn [set_ctx ls_ctx cx_frames]. rewrite W8. reflexivity.
    + cbn [set_ctx ls_ctx cx_used]. exact W8.
Qed.

Lemma blocks_of_set_ctx : forall c (s : LS), cx_vals c = cx_vals (ls_ctx s) -> cx_head c = cx_head (ls_ctx s) ->
  cx_indexes c = cx_indexes (ls_ctx s) -> blocks_of (set_ctx c s) = blocks_of s.
Proof. intros c s E1 E2 E3. unfold blocks_of. cbn [set_ctx ls_b1 ls_b2 ls_b3 ls_b4 ls_b5 ls_ctx]. rewrite E1, E2, E3. reflexivity. Qed.

(* [comment removed for export] *)
Lemma own_setbn_same : forall r b' (s : LS) X, st_ok s -> valid_ref r s -> own s X ->
  bn_blocks b' = bn_blocks (getbn r s) -> own (setbn r b' s) X.
Proof.
  intros r b' s X Hs Hv Ho E. destruct (blocks_setbn r s Hs Hv) as (R & H1 & H2). unfold own in *.
  eapply Permutation_trans; [exact Ho|]. eapply Permutation_trans; [exact H1|]. rewrite <- E. apply Permutation_sym, H2.
Qed.

Lemma bn_blocks_same : forall (b b' : BN), bn_d b' = bn_d b -> length (bn_buf b') = length (bn_buf b) -> bn_blocks b' = bn_blocks b.
Proof. intros b b' E1 E2. unfold bn_blocks, bn_dmax. rewrite E1, E2. reflexivity. Qed.

Lemma bn_ok_zero : forall b : BN, bn_ok b -> bn_ok (bn_zero_pure b).
Proof. intros b (H1 & H2 & H3 & H4). unfold bn_ok, bn_zero_pure, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. repeat split; try assumption; lia. Qed.

Lemma st_ok_getbn : forall r (s : LS), st_ok s -> valid_ref r s -> bn_ok (getbn r s).
Proof.
  intros r s Hs Hv. pose proof Hs as (H1 & H2 & H3 & H4 & H5 & _). destruct r as [| | | | |i]; try assumption.
  destruct Hv as [Hi Hne]. destruct (st_ok_pool s Hs Hne) as (p0 & p1 & p2 & E & Hp0 & Hp1 & Hp2).
  cbn [getbn]. rewrite E. assert (i = 0 \/ i = 1 \/ i = 2)%nat as [->|[->| ->]] by lia; assumption.
Qed.

Lemma BN_CTX_get_spec : forall s X k (Q : bnref -> LS -> blocks -> Prop),
  st_ok s -> own s X -> ctx_wf (ls_ctx s) -> cx_frames (ls_ctx s) = [0%nat] -> cx_used (ls_ctx s) = k -> (k < 3)%nat ->
  (forall s' X', valid_ref (RPool k) s' -> getbn (RPool k) s' = bn_zero_pure (getbn (RPool k) s) ->
                 (forall r, r <> RPool k -> getbn r s' = getbn r s) -> st_ok s' -> own s' X' -> ctx_wf (ls_ctx s') ->
                 cx_frames (ls_ctx s') = [0%nat] -> cx_used (ls_ctx s') = S k -> Q (RPool k) s' X') ->
  bwp (BN_CTX_get ops) s X Q.
Proof.
  intros s X k Q Hs Ho (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8) Hfr Hk Hk3 HQ. unfold BN_CTX_get.
  apply bwp_bind, bwp_getctx. set (c := ls_ctx s) in *. rewrite W1, W2. cbn [Nat.eqb negb orb].
  apply bwp_bind.
  destruct W5 as [(P1 & P2 & P3 & P4)|(P1 & P2)].
  - (* [comment removed for export] *)
    assert (Ek : k = 0%nat) by lia. rewrite Ek in *. clear Ek. rewrite W3, P4, P1. cbn [Nat.eqb negb].
    apply bwp_bind, bwp_malloc.
    { eapply own_ok_bn; [exact Hs|exact Ho|]. unfold BSZ, POOL_ITEM_BYTES. lia. }
    intros p Hp. apply bwp_bind, bwp_setctx, bwp_ret.
    set (c1 := mkCtx (Some p) (Some p) (repeat (bn_nil 0) BN_CTX_POOL_SIZE) 1 BN_CTX_POOL_SIZE (cx_indexes c) (cx_frames c) (cx_ssize c) 0 0 false).
    set (s1 := set_ctx c1 s).
    assert (Hs1 : st_ok s1).
    { apply st_ok_set_ctx; [exact Hs|]. right. exists (bn_nil 0), (bn_nil 0), (bn_nil 0).
      split; [reflexivity|]. repeat split; apply bn_ok_nil; left; reflexivity. }
    assert (Ho1 : own s1 ((p, POOL_ITEM_BYTES) :: X)).
    { unfold own in *. unfold blocks_of in *. subst s1 c1. cbn [set_ctx ls_b1 ls_b2 ls_b3 ls_b4 ls_b5 ls_ctx cx_vals cx_head cx_indexes opt_block].
      fold c in Ho. rewrite P2, P3 in Ho. cbn [map concat opt_block app] in Ho.
      change BN_CTX_POOL_SIZE with 16%nat. rewrite concat_nil_blocks. cbn [app].
      rewrite !app_assoc. apply Permutation_cons_app. rewrite <- !app_assoc. exact Ho. }
    apply bwp_bind, bwp_get. apply bwp_bind, bwp_set. apply bwp_bind, bwp_getctx. apply bwp_bind, bwp_setctx, bwp_ret.
    assert (Eset : setbn (RPool 0) (bn_zero_pure (getbn (RPool 0) s1)) s1 = s1) by reflexivity.
    rewrite Eset. subst s1 c1. cbn [set_ctx ls_ctx cx_head cx_current cx_vals cx_pused cx_psize cx_indexes cx_frames cx_ssize cx_used
                                      ls_b1 ls_b2 ls_b3 ls_b4 ls_b5] in *.
    apply HQ.
    + split; [lia|]. cbn [ls_ctx cx_vals]. discriminate.
    + cbn [getbn set_ctx ls_ctx cx_vals]. fold c. rewrite P2. reflexivity.
    + intros r Hr. destruct r as [| | | | |j]; try reflexivity. cbn [getbn set_ctx ls_ctx cx_vals]. fold c. rewrite P2.
      destruct j as [|j]; [congruence|]. change BN_CTX_POOL_SIZE with 16%nat.
      destruct (Nat.lt_ge_cases (S j) 16) as [Hlt|Hge].
      * rewrite nth_repeat. destruct j; reflexivity.
      * rewrite !nth_overflow; [reflexivity|cbn [length]; lia|rewrite repeat_length; lia].
    + exact Hs1.
    + exact Ho1.
    + unfold ctx_wf. cbn [set_ctx ls_ctx cx_err_stack cx_too_many cx_pused cx_used cx_psize cx_vals cx_head cx_ssize cx_frames cx_indexes].
      fold c. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
      split; [right; split; [reflexivity|discriminate]|]. split; [exact W6|]. split; [exact W7|]. intros E; rewrite Hfr in E; discriminate.
    + cbn [set_ctx ls_ctx cx_frames]. exact Hfr.
    + reflexivity.
  - (* [comment removed for export] *)
    assert (Hne : (cx_pused c =? cx_psize c)%nat = false) by (apply Nat.eqb_neq; lia).
    rewrite Hne. assert (Epu : cx_pused c = k) by lia. rewrite Epu. apply bwp_bind, bwp_setctx, bwp_ret.
    set (c1 := mkCtx (cx_head c) (if (k =? 0)%nat then cx_head c else cx_current c) (cx_vals c) (S k) (cx_psize c)
                     (cx_indexes c) (cx_frames c) (cx_ssize c) (cx_used c) 0 false).
    set (s1 := set_ctx c1 s).
    assert (Hs1 : st_ok s1) by (apply st_ok_set_ctx; [exact Hs|]; destruct Hs as (_ & _ & _ & _ & _ & Hp'); exact Hp').
    assert (Ho1 : own s1 X) by (unfold own; subst s1; rewrite blocks_of_set_ctx by reflexivity; exact Ho).
    assert (Hv1 : valid_ref (RPool k) s1) by (split; [lia|exact P2]).
    assert (Eg : forall r, getbn r s1 = getbn r s) by (intros r; apply getbn_set_ctx; reflexivity).
    apply bwp_bind, bwp_get. apply bwp_bind, bwp_set. apply bwp_bind, bwp_getctx. apply bwp_bind, bwp_setctx, bwp_ret.
    set (zb := bn_zero_pure (getbn (RPool k) s1)).
    set (s2 := setbn (RPool k) zb s1).
    assert (Hzb : bn_ok zb) by (apply bn_ok_zero, st_ok_getbn; assumption).
    assert (Hs2 : st_ok s2) by (apply st_ok_setbn; assumption).
    assert (Ho2 : own s2 X) by (apply own_setbn_same; try assumption; reflexivity).
    pose proof (ctx_same_setbn (RPool k) zb s1) as Hsame. fold s2 in Hsame.
    destruct Hsame as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
    set (c3 := mkCtx _ _ _ _ _ _ _ _ _ _ _).
    assert (Ev3 : cx_vals c3 = cx_vals (ls_ctx s2)) by reflexivity.
    apply HQ.
    + split; [lia|]. cbn [set_ctx ls_ctx]. rewrite Ev3. intros E. apply A11 in E. subst s1. cbn [set_ctx ls_ctx] in E. subst c1. cbn [cx_vals] in E. contradiction.
    + rewrite getbn_set_ctx by exact Ev3. subst s2. rewrite getbn_setbn_same by assumption. subst zb. rewrite Eg. reflexivity.
    + intros r Hr. rewrite getbn_set_ctx by exact Ev3. subst s2. rewrite getbn_setbn_other by congruence. apply Eg.
    + apply st_ok_set_ctx; [exact Hs2|]. rewrite Ev3. destruct Hs2 as (_ & _ & _ & _ & _ & Hp'). exact Hp'.
    + unfold own. rewrite blocks_of_set_ctx; [exact Ho2|exact Ev3|subst c3; reflexivity|subst c3; reflexivity].
    + unfold ctx_wf. subst c3. cbn [set_ctx ls_ctx cx_err_stack cx_too_many cx_pused cx_used cx_psize cx_vals cx_head cx_ssize cx_frames cx_indexes].
      rewrite A3, A4, A6, A7, A8. subst s1 c1. cbn [set_ctx ls_ctx cx_pused cx_psize cx_frames cx_ssize cx_used].
      rewrite Hk. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
      split; [right; split; [exact P1|]|].
      { intros E. apply A11 in E. cbn [set_ctx ls_ctx cx_vals] in E. contradiction. }
      split; [exact W6|]. split; [exact W7|]. intros E; rewrite Hfr in E; discriminate.
    + subst c3. cbn [set_ctx ls_ctx cx_frames]. rewrite A6. subst s1 c1. cbn [set_ctx ls_ctx cx_frames]. exact Hfr.
    + subst c3. cbn [set_ctx ls_ctx cx_used]. rewrite A8. subst s1 c1. cbn [set_ctx ls_ctx cx_used]. rewrite Hk. reflexivity.
Qed.

Lemma BN_CTX_end_spec : forall s X (Q : unit -> LS -> blocks -> Prop),
  st_ok s -> own s X -> ctx_wf (ls_ctx s) -> cx_frames (ls_ctx s) = [0%nat] ->
  (forall s', (forall r, getbn r s' = getbn r s) -> st_ok s' -> own s' X -> ctx_rest (ls_ctx s') -> Q tt s' X) ->
  bwp (BN_CTX_end ops) s X Q.
Proof.
  intros s X Q Hs Ho (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8) Hfr HQ. unfold BN_CTX_end.
  apply bwp_bind, bwp_getctx. set (c := ls_ctx s) in *. rewrite W1. cbn [Nat.eqb negb]. rewrite Hfr. cbn [rev app].
  apply bwp_setctx. set (c' := mkCtx _ _ _ _ _ _ _ _ _ _ _).
  assert (Ev : cx_vals c' = cx_vals (ls_ctx s)) by reflexivity.
  apply HQ.
  - intros r. apply getbn_set_ctx. exact Ev.
  - apply st_ok_set_ctx; [exact Hs|]. rewrite Ev. destruct Hs as (_ & _ & _ & _ & _ & Hp'). exact Hp'.
  - unfold own. rewrite blocks_of_set_ctx; [exact Ho|exact Ev|reflexivity|reflexivity].
  - split; [|reflexivity]. unfold ctx_wf. subst c'.
    cbn [set_ctx ls_ctx cx_err_stack cx_too_many cx_pused cx_used cx_psize cx_vals cx_head cx_ssize cx_frames cx_indexes].
    fold c. split; [reflexivity|]. split; [reflexivity|].
    split; [destruct (Nat.ltb_spec 0 (cx_used c)); lia|]. split; [lia|].
    split.
    { destruct W5 as [(P1 & P2 & P3 & P4)|(P1 & P2)]; [left; tauto|right; tauto]. }
    split.
    { destruct W6 as [(S1 & S2 & S3)|S1]; [rewrite Hfr in S2; discriminate|right; exact S1]. }
    split; [left; reflexivity|reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bnref_eqb_neq : forall r r', r <> r' -> bnref_eqb r r' = false.
Proof.
  intros r r' H. destruct r as [| | | | |i]; destruct r' as [| | | | |j]; try reflexivity; try congruence.
  cbn [bnref_eqb]. apply Nat.eqb_neq. congruence.
Qed.

Lemma flags_land_0 : forall (b : BN) m, bn_ok b -> (m = 2 \/ m = 4 \/ m = 8) -> (Z.land (bn_flags b) m =? 0) = true.
Proof. intros b m (_ & _ & _ & [E|E]) [-> |[-> | ->]]; rewrite E; reflexivity. Qed.

Lemma BN_copy_spec : forall ra rb s X (Q : unit -> LS -> blocks -> Prop),
  st_ok s -> own s X -> valid_ref ra s -> valid_ref rb s -> ra <> rb ->
  (forall a' X', let b := getbn rb s in
     bn_ok a' -> bn_top a' = bn_top b -> bn_neg a' = bn_neg b -> bn_flags a' = bn_flags (getbn ra s) ->
     firstn (bn_top b) (bn_buf a') = firstn (bn_top b) (bn_buf b) ->
     st_ok (setbn ra a' s) -> own (setbn ra a' s) X' -> Q tt (setbn ra a' s) X') ->
  bwp (BN_copy ops ra rb) s X Q.
Proof.
  intros ra rb s X Q Hs Ho Hva Hvb Hne HQ. unfold BN_copy.
  apply bwp_bind, bwp_get. set (b := getbn rb s) in *.
  assert (Hb : bn_ok b) by (apply st_ok_getbn; assumption).
  unfold BN_FLG_CONSTTIME. rewrite (flags_land_0 b 4 Hb) by tauto. cbn [negb].
  rewrite (bnref_eqb_neq ra rb Hne).
  apply bwp_bind. apply bn_wexpand_spec; try assumption; [apply st_ok_getbn; assumption| |].
  { destruct Hb as (_ & Hb2 & Hb3 & _). lia. }
  intros a1 X1 (E1 & E2 & E3 & E4 & Ha1 & E5 & E6) Hs1 Ho1.
  assert (Hva1 : valid_ref ra (setbn ra a1 s)) by (apply valid_ref_setbn; exact Hva).
  apply bwp_bind, bwp_get. rewrite getbn_setbn_same by assumption.
  apply bwp_set. rewrite setbn_setbn_same.
  set (a2 := mkBN (bn_d a1) (if (0 <? bn_top b)%nat then splice (bn_buf a1) 0 (firstn (bn_top b) (bn_buf b)) else bn_buf a1)
                  (bn_top b) (bn_neg b) (bn_flags a1)).
  destruct Hb as (Hb1 & Hb2 & Hb3 & Hb4). destruct Ha1 as (Ha11 & Ha12 & Ha13 & Ha14). unfold bn_dmax in *.
  assert (Hfl : length (firstn (bn_top b) (bn_buf b)) = bn_top b) by (apply firstn_length_le; lia).
  assert (Hlen : length (bn_buf a2) = length (bn_buf a1)).
  { subst a2. cbn [bn_buf]. destruct (0 <? bn_top b)%nat; [|reflexivity]. apply splice_length. lia. }
  assert (Ha2 : bn_ok a2).
  { unfold bn_ok, bn_dmax. rewrite Hlen. subst a2. cbn [bn_buf bn_top bn_flags].
    split; [|split; [lia|split; assumption]].
    destruct (0 <? bn_top b)%nat; [|exact Ha11]. apply splice_limbs; [exact Ha11|apply limbs_firstn; exact Hb1]. }
  apply HQ; try assumption; try reflexivity.
  - subst a2. cbn [bn_buf]. destruct (Nat.ltb_spec 0 (bn_top b)) as [Hpos|Hz].
    + apply firstn_splice_0; lia.
    + replace (bn_top b) with 0%nat by lia. reflexivity.
  - rewrite <- (setbn_setbn_same ra a1 a2 s). apply st_ok_setbn; assumption.
  - rewrite <- (setbn_setbn_same ra a1 a2 s). apply own_setbn_same; try assumption.
    rewrite getbn_setbn_same by assumption. apply bn_blocks_same; [reflexivity|exact Hlen].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bwp_update : forall r b' s X (Q : unit -> LS -> blocks -> Prop),
  st_ok s -> own s X -> valid_ref r s -> bn_ok b' -> bn_blocks b' = bn_blocks (getbn r s) ->
  (st_ok (setbn r b' s) -> own (setbn r b' s) X -> Q tt (setbn r b' s) X) ->
  bwp (bset ops r b') s X Q.
Proof.
  intros r b' s X Q Hs Ho Hv Hb' Hbl HQ. apply bwp_set. apply HQ.
  - apply st_ok_setbn; assumption.
  - apply own_setbn_same; assumption.
Qed.

Lemma BN_set_negative_spec : forall r sgn s X (Q : unit -> LS -> blocks -> Prop),
  st_ok s -> own s X -> valid_ref r s ->
  (let b' := bn_with_neg (getbn r s) (sgn && negb (bn_top (getbn r s) =? 0)%nat) in
   st_ok (setbn r b' s) -> own (setbn r b' s) X -> Q tt (setbn r b' s) X) ->
  bwp (BN_set_negative ops r sgn) s X Q.
Proof.
  intros r sgn s X Q Hs Ho Hv HQ. unfold BN_set_negative. apply bwp_bind, bwp_get.
  apply bwp_update; try assumption; [|reflexivity].
  pose proof (st_ok_getbn r s Hs Hv) as (H1 & H2 & H3 & H4). unfold bn_ok, bn_with_neg, bn_dmax in *.
  cbn [bn_buf bn_top bn_flags]. tauto.
Qed.

End Specs.
