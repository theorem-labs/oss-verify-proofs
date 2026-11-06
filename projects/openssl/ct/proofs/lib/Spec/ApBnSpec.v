(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim PrintfModel BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnDivWords BnSpecs
  BgState BgLib BgInv BgSpecs BgLibSpec BgShiftSpec BgAddSpec BgWordSpec ApBase ApState ApLogic ApFmt ApBn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pf_elem_seg {A} (S R : list A) (e : A) : Permutation (S ++ e :: R) (e :: S ++ R).
Proof. apply Permutation_sym. apply Permutation_middle. Qed.
Lemma pf_seg_elem {A} (Sg R : list A) (x : A) : Permutation (x :: Sg ++ R) (Sg ++ x :: R).
Proof. apply Permutation_middle. Qed.
Lemma pf_seg_nil {A} (Sg : list A) : Permutation Sg (Sg ++ []).
Proof. rewrite app_nil_r. apply Permutation_refl. Qed.
Lemma pf_elem_nil {A} (e : A) : Permutation [e] (e :: []).
Proof. apply Permutation_refl. Qed.

Ltac pg := match goal with |- ?g => idtac g end.

(* [comment removed for export] *)
Ltac pfront e :=
  lazymatch goal with
  | |- Permutation (e :: _) _ => apply Permutation_refl
  | |- Permutation (?x :: _) _ => eapply Permutation_trans; [apply perm_skip; pfront e|apply perm_swap]
  | |- Permutation (?S ++ _) _ => eapply Permutation_trans; [apply Permutation_app_head; pfront e|apply pf_elem_seg]
  end.
(* [comment removed for export] *)
Ltac psfront Sg :=
  lazymatch goal with
  | |- Permutation (Sg ++ _) _ => apply Permutation_refl
  | |- Permutation Sg _ => apply pf_seg_nil
  | |- Permutation (?x :: _) _ => eapply Permutation_trans; [apply perm_skip; psfront Sg|apply pf_seg_elem]
  | |- Permutation (?S ++ _) _ => eapply Permutation_trans; [apply Permutation_app_head; psfront Sg|apply Permutation_app_swap_app]
  end.
Ltac perm_norm := cbn [app]; repeat (rewrite <- app_assoc || rewrite <- app_comm_cons); cbn [app].
Ltac perm_solve :=
  perm_norm;
  lazymatch goal with
  | |- Permutation ?L ?L => apply Permutation_refl
  | |- Permutation _ [] => apply Permutation_refl
  | |- Permutation _ (?e :: _) => eapply Permutation_trans; [pfront e|]; apply perm_skip; perm_solve
  | |- Permutation _ (?S ++ _) => eapply Permutation_trans; [psfront S|]; apply Permutation_app_head; perm_solve
  | |- Permutation _ ?S => eapply Permutation_trans; [psfront S|]; rewrite app_nil_r; apply Permutation_refl
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section BnSpec.
Context {ptr : Type}.
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ST := (bstate ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).
Local Notation okA := (okAp (ptr:=ptr) AP_NB AP_TOT) (only parsing).
Local Notation bwp := (bwp (okAp (ptr:=ptr) AP_NB AP_TOT)) (only parsing).

(* [comment removed for export] *)
Definition bnw (b : BN) (v : Z) : Prop :=
  limbs (bn_buf b) /\ (bn_top b <= length (bn_buf b))%nat /\ bn_mag b = v /\ bn_neg b = false
  /\ bn_flags b = BN_FLG_MALLOCED /\ (bn_d b = None <-> bn_buf b = []).
Definition bnv (b : BN) (v : Z) : Prop := bnw b v /\ bn_norm b.
Lemma bnv_w (b : BN) v : bnv b v -> bnw b v. Proof. intros [H _]; exact H. Qed.

Definition bnb (b : BN) : list (ptr * Z) := match bn_d b with Some p => [(p, 8 * Z.of_nat (length (bn_buf b)))] | None => [] end.
Definition bdm (b : BN) : Z := Z.of_nat (length (bn_buf b)).

(* [comment removed for export] *)
Definition st2 (s : ST) : Prop := length (st_bns s) = 2%nat.

Lemma getbn_setbn_same2 r (b : BN) (s : ST) : st2 s -> (r < 2)%nat -> getbn r (setbn r b s) = b.
Proof. intros H Hr. unfold getbn, setbn, set_bns. cbn. apply nth_list_set_same. rewrite H. exact Hr. Qed.
Lemma getbn_setbn_other2 r r' (b : BN) (s : ST) : r <> r' -> getbn r' (setbn r b s) = getbn r' s.
Proof. intros H. unfold getbn, setbn, set_bns. cbn. apply nth_list_set_other. exact H. Qed.
Lemma st2_setbn r (b : BN) (s : ST) : st2 s -> st2 (setbn r b s).
Proof. intros H. unfold st2, setbn, set_bns in *. cbn. rewrite list_set_length. exact H. Qed.

(* [comment removed for export] *)
Lemma skipn_firstn_one : forall (l : list Z) t, (S t <= length l)%nat -> skipn t (firstn (S t) l) = [nth t l 0].
Proof.
  induction l as [|x l IH]; intros [|t] H; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.

Lemma lval_top_nonzero : forall l t, limbs l -> (S t <= length l)%nat -> nth t l 0 <> 0 -> Bp t <= lval (firstn (S t) l).
Proof.
  intros l t Hl Ht Hnz.
  rewrite (lval_split_le t (firstn (S t) l)) by (rewrite firstn_length_le; lia).
  rewrite firstn_firstn, Nat.min_l by lia. rewrite skipn_firstn_one by exact Ht. cbn [lval].
  pose proof (limbs_nth l t Hl) as [H0 H1]. pose proof (lval_nonneg (firstn t l) (limbs_firstn _ _ Hl)). pose proof (Bp_pos t). nia.
Qed.

Lemma bnv_bounds (b : BN) v : bnv b v -> 0 <= v < Bp (bn_top b) /\ ((0 < bn_top b)%nat -> Bp (bn_top b - 1) <= v).
Proof.
  intros ((Hl & Ht & Hm & Hn & Hf & Hd) & Hnorm). unfold bn_mag in Hm. subst v.
  assert (Hlf : limbs (firstn (bn_top b) (bn_buf b))) by (apply limbs_firstn; exact Hl).
  assert (Hlen : length (firstn (bn_top b) (bn_buf b)) = bn_top b) by (apply firstn_length_le; exact Ht).
  pose proof (lval_bound _ Hlf) as B. rewrite Hlen in B.
  split; [exact B|]. intros Hpos. destruct Hnorm as [E0|Hnz]; [lia|].
  destruct (bn_top b) as [|t] eqn:Et; [lia|]. replace (S t - 1)%nat with t in * by lia. apply lval_top_nonzero; assumption.
Qed.

Lemma bnv_zero_iff (b : BN) v : bnv b v -> (bn_top b = 0%nat <-> v = 0).
Proof.
  intros H. pose proof (bnv_bounds b v H) as [B1 B2]. split.
  - intros E. rewrite E in B1. cbn in B1. unfold Bp in B1. cbn in B1. lia.
  - intros ->. destruct (bn_top b); [reflexivity|]. exfalso. specialize (B2 ltac:(lia)). pose proof (Bp_pos (S n - 1)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition roomy0 (X0 : list (ptr * Z)) : Prop :=
  forall L n, zlength L <= 8 -> bnonneg L -> 0 <= n -> bsum L + n <= 16000 -> okA (L ++ X0) n.

Lemma bnb_facts (b : BN) v : bnw b v -> zlength (bnb b) <= 1 /\ bsum (bnb b) = 8 * bdm b /\ bnonneg (bnb b) /\ 0 <= bdm b.
Proof.
  intros (Hl & Ht & Hm & Hn & Hf & Hd). unfold bnb, bdm, zlength. destruct (bn_d b) as [p|].
  - cbn. unfold bsum; cbn. split; [lia|]. split; [lia|]. split; [apply Forall_cons; [cbn; lia|apply Forall_nil]|lia].
  - cbn. destruct Hd as [Hd _]. rewrite (Hd eq_refl). cbn. unfold bsum; cbn. split; [lia|]. split; [lia|]. split; [apply Forall_nil|lia].
Qed.

Lemma okAp_perm (X Y : list (ptr * Z)) n : Permutation X Y -> okA X n -> okA Y n.
Proof.
  intros HP (A & B & C & D). unfold okAp. rewrite <- (zlen_perm _ _ HP), <- (bsum_perm _ _ HP). repeat split; try assumption. eapply bnonneg_perm; [exact HP|exact C].
Qed.

(* [comment removed for export] *)
Lemma ok_bn : forall X L' X0 n, roomy0 X0 -> Permutation X (L' ++ X0) -> zlength L' <= 8 -> bnonneg L' -> 0 <= n -> bsum L' + n <= 16000 -> okA X n.
Proof. intros X L' X0 n HR HP HL HLn Hn Hb. eapply okAp_perm; [apply Permutation_sym; exact HP|]. apply HR; assumption. Qed.

Lemma lt62c n : 0 <= n <= 100000 -> 0 <= n < 2^62.
Proof. intros H. assert (E : 2^62 = 4611686018427387904) by reflexivity. rewrite E. lia. Qed.

(* [comment removed for export] *)
Lemma bn_wexpand_bwp : forall r (words : nat) (bs : ST) v L X0 X (Q : unit * ST -> list (ptr * Z) -> Prop),
  st2 bs -> (r < 2)%nat -> bnw (getbn r bs) v -> (Z.of_nat words <= 512) -> roomy0 X0 ->
  Permutation X (bnb (getbn r bs) ++ L ++ X0) -> zlength L <= 6 -> bnonneg L -> bsum L + 8 * bdm (getbn r bs) + 8 * Z.of_nat words <= 16000 ->
  (forall b' X', bnw b' v -> (bn_norm (getbn r bs) -> bn_norm b') -> bn_top b' = bn_top (getbn r bs) -> bdm b' = Z.max (bdm (getbn r bs)) (Z.of_nat words) ->
                bn_flags b' = bn_flags (getbn r bs) -> firstn (bn_top b') (bn_buf b') = firstn (bn_top (getbn r bs)) (bn_buf (getbn r bs)) ->
                Permutation X' (bnb b' ++ L ++ X0) -> Q (tt, setbn r b' bs) X') ->
  bwp (bn_wexpand ops r words bs) X Q.
Proof.
  intros r words bs v L X0 X Q H2 Hr Hb Hw HR HP HLc HLn Hsz HQ.
  pose proof Hb as (Hl & Ht & Hm & Hn & Hf & Hd). destruct (bnb_facts _ _ Hb) as (B1 & B2 & B3 & B4).
  unfold bn_wexpand. cbn -[bmalloc bfree_opt Nat.leb Z.ltb Z.of_nat has_flag getbn setbn BN_WORDS_MAX Z.mul app firstn repeat].
  destruct (Nat.leb_spec words (bn_dmax (getbn r bs))) as [Hle|Hgt].
  - cbn. pose proof (HQ (getbn r bs) X Hb (fun H => H) eq_refl) as HQ'. rewrite setbn_getbn_id in HQ'. apply HQ'; [unfold bdm, bn_dmax in *; lia|reflexivity|reflexivity|exact HP].
  - destruct (Z.ltb_spec BN_WORDS_MAX (Z.of_nat words)) as [C|C]; [unfold BN_WORDS_MAX in C; exfalso; lia|].
    destruct (Z.ltb_spec 512 (Z.of_nat words)) as [C2|C2]; [exfalso; lia|].
    unfold has_flag. rewrite Hf. cbn -[bmalloc bfree_opt getbn setbn Z.mul app firstn repeat Z.of_nat].
    (* [comment removed for export] *)
    split; [apply lt62c; lia|]. split.
    { apply (ok_bn X (bnb (getbn r bs) ++ L) X0); [exact HR|rewrite <- app_assoc; exact HP|rewrite zlen_app'; lia|apply bnonneg_app; assumption|lia|rewrite bsum_app; lia]. }
    split; [reflexivity|]. intros p Hp. cbn -[getbn setbn firstn repeat app Z.mul Z.of_nat bfree_opt].
    set (b' := {| bn_d := Some p; bn_buf := firstn (bn_top (getbn r bs)) (bn_buf (getbn r bs)) ++ repeat 0 (words - bn_top (getbn r bs));
                  bn_top := bn_top (getbn r bs); bn_neg := bn_neg (getbn r bs); bn_flags := BN_FLG_MALLOCED |}).
    assert (Hlen' : length (bn_buf b') = words).
    { unfold b'; cbn. rewrite length_app, repeat_length, firstn_length_le by exact Ht. unfold bn_dmax in Hgt. lia. }
    assert (Hfn0 : firstn (bn_top (getbn r bs)) (firstn (bn_top (getbn r bs)) (bn_buf (getbn r bs)) ++ repeat 0 (words - bn_top (getbn r bs))) = firstn (bn_top (getbn r bs)) (bn_buf (getbn r bs))).
    { rewrite firstn_app, firstn_firstn, Nat.min_id, firstn_length_le by exact Ht. rewrite Nat.sub_diag. cbn. rewrite app_nil_r. reflexivity. }
    assert (Hnorm' : bn_norm (getbn r bs) -> bn_norm b').
    { unfold bn_norm, b'; cbn -[firstn repeat app Nat.sub]. intros [E0|Hnz]; [left; exact E0|].
      destruct (Nat.eq_dec (bn_top (getbn r bs)) 0) as [E0|NE]; [left; exact E0|right].
      rewrite app_nth1 by (rewrite firstn_length_le by exact Ht; lia).
      rewrite nth_firstn. destruct (Nat.ltb_spec (bn_top (getbn r bs) - 1) (bn_top (getbn r bs))); [exact Hnz|lia]. }
    assert (Hb' : bnw b' v).
    { unfold bnw, b', bn_mag in *; cbn -[firstn repeat app]. rewrite Hn.
      assert (Hfn : firstn (bn_top (getbn r bs)) (firstn (bn_top (getbn r bs)) (bn_buf (getbn r bs)) ++ repeat 0 (words - bn_top (getbn r bs))) = firstn (bn_top (getbn r bs)) (bn_buf (getbn r bs))).
      { rewrite firstn_app, firstn_firstn, Nat.min_id, firstn_length_le by exact Ht. rewrite Nat.sub_diag. cbn. rewrite app_nil_r. reflexivity. }
      split; [apply limbs_app; [apply limbs_firstn; exact Hl|apply limbs_repeat; apply limb_0]|].
      split; [cbn in Hlen'; rewrite length_app, repeat_length, firstn_length_le by exact Ht; unfold bn_dmax in Hgt; lia|].
      split; [rewrite Hfn; exact Hm|]. split; [reflexivity|].
      split; [reflexivity|]. split; [intros C3; discriminate|]. intros E. apply (f_equal (@length Z)) in E. cbn in E. cbn in Hlen'. rewrite Hlen' in E. unfold bn_dmax in Hgt. lia. }
    destruct (bn_d (getbn r bs)) as [q|] eqn:Ed; cbn -[getbn setbn firstn repeat app Z.mul Z.of_nat].
    + (* [comment removed for export] *)
      exists (8 * bdm (getbn r bs)), ((p, 8 * Z.of_nat words) :: L ++ X0). split.
      { transitivity ((p, 8 * Z.of_nat words) :: bnb (getbn r bs) ++ L ++ X0); [apply perm_skip; exact HP|]. unfold bnb. rewrite Ed. unfold bdm. cbn. apply perm_swap. }
      apply HQ; [exact Hb'|exact Hnorm'|reflexivity|unfold bdm; cbn in Hlen' |- *; rewrite Hlen'; unfold bn_dmax in Hgt; lia|unfold b'; cbn; symmetry; exact Hf|unfold b'; cbn -[firstn app repeat]; exact Hfn0|].
      unfold bnb. cbn -[Z.mul Z.of_nat app firstn repeat]. cbn in Hlen'. rewrite Hlen'. apply Permutation_refl.
    + apply HQ; [exact Hb'|exact Hnorm'|reflexivity|unfold bdm; cbn in Hlen' |- *; rewrite Hlen'; unfold bn_dmax in Hgt; lia|unfold b'; cbn; symmetry; exact Hf|unfold b'; cbn -[firstn app repeat]; exact Hfn0|].
      unfold bnb at 1. cbn -[Z.mul Z.of_nat app firstn repeat bnb]. cbn in Hlen'. rewrite Hlen'.
      transitivity ((p, 8 * Z.of_nat words) :: bnb (getbn r bs) ++ L ++ X0); [apply perm_skip; exact HP|]. unfold bnb. rewrite Ed. cbn. apply Permutation_refl.
Qed.

(* [comment removed for export] *)
Lemma bwp_bbind : forall {A B} (m : BM (M:=btree ptr) (ptr:=ptr) A) (f : A -> BM (M:=btree ptr) (ptr:=ptr) B) (s : ST) X Q,
  bwp (m s) X (fun r X' => bwp (f (fst r) (snd r)) X' Q) -> bwp (bbind ops m f s) X Q.
Proof. intros. unfold bbind. cbn [bind tree_ops]. apply bwp_bind. exact H. Qed.

Lemma BN_new_bwp : forall r (bs : ST) L X0 X (Q : ptr * ST -> list (ptr * Z) -> Prop),
  st2 bs -> (r < 2)%nat -> roomy0 X0 -> Permutation X (L ++ X0) -> zlength L <= 7 -> bnonneg L -> bsum L + 24 <= 16000 ->
  (forall p X', Permutation X' ((p, 24) :: L ++ X0) -> Q (p, setbn r (bn_nil BN_FLG_MALLOCED) bs) X') ->
  bwp (BN_new ops r bs) X Q.
Proof.
  intros r bs L X0 X Q H2 Hr HR HP HLc HLn Hsz HQ. unfold BN_new. cbn -[setbn].
  split; [apply lt62c; unfold BN_STRUCT_BYTES; lia|]. split; [apply (ok_bn X L X0); try assumption; unfold BN_STRUCT_BYTES; lia|]. split; [reflexivity|].
  intros p Hp. unfold BN_STRUCT_BYTES. apply HQ. apply perm_skip. exact HP.
Qed.

Lemma bnv_nil : bnv (bn_nil (ptr:=ptr) BN_FLG_MALLOCED) 0.
Proof. unfold bnv, bnw, bn_nil, bn_mag, bn_norm; cbn. repeat split; try lia; try constructor; auto. Qed.

Lemma BN_free_bwp : forall r (bs : ST) p v L X0 X (Q : unit * ST -> list (ptr * Z) -> Prop),
  st2 bs -> (r < 2)%nat -> bnv (getbn r bs) v -> Permutation X ((p, 24) :: bnb (getbn r bs) ++ L ++ X0) ->
  (forall X', Permutation X' (L ++ X0) -> Q (tt, setbn r (bn_nil 0) bs) X') ->
  bwp (BN_free ops r (Some p) bs) X Q.
Proof.
  intros r bs p v L X0 X Q H2 Hr Hb HP HQ. pose proof Hb as ((Hl & Ht & Hm & Hn & Hf & Hd) & Hnorm).
  unfold BN_free, has_flag. cbn -[setbn getbn Z.land Z.eqb bfree_opt]. rewrite Hf. cbn -[setbn getbn bfree_opt].
  unfold bnb in HP. destruct (bn_d (getbn r bs)) as [q|] eqn:Ed; cbn -[setbn getbn].
  - eexists _, ((p, 24) :: L ++ X0). split; [transitivity ((p, 24) :: (q, 8 * Z.of_nat (length (bn_buf (getbn r bs)))) :: L ++ X0); [exact HP|apply perm_swap]|].
    exists 24, (L ++ X0). split; [apply Permutation_refl|]. apply HQ. apply Permutation_refl.
  - exists 24, (L ++ X0). split; [exact HP|]. apply HQ. apply Permutation_refl.
Qed.

Lemma BN_set_word_bwp : forall r w (bs : ST) v L X0 X (Q : unit * ST -> list (ptr * Z) -> Prop),
  st2 bs -> (r < 2)%nat -> bnw (getbn r bs) v -> 0 <= w < BW -> roomy0 X0 ->
  Permutation X (bnb (getbn r bs) ++ L ++ X0) -> zlength L <= 6 -> bnonneg L -> bsum L + 8 * bdm (getbn r bs) + 8 <= 16000 ->
  (forall b' X', bnv b' w -> bdm b' = Z.max (bdm (getbn r bs)) 1 -> (bn_top b' <= 1)%nat -> Permutation X' (bnb b' ++ L ++ X0) -> Q (tt, setbn r b' bs) X') ->
  bwp (BN_set_word ops r w bs) X Q.
Proof.
  intros r w bs v L X0 X Q H2 Hr Hb Hw HR HP HLc HLn Hsz HQ. unfold BN_set_word. apply bwp_bbind.
  eapply bn_wexpand_bwp; [exact H2|exact Hr|exact Hb|cbn; lia|exact HR|exact HP|exact HLc|exact HLn|cbn; lia|].
  intros b1 X1 Hb1 _ Ht1 Hd1 Hf1 _ HP1. cbn -[setbn getbn upd Z.eqb].
  rewrite (getbn_setbn_same2 r b1 bs H2 Hr). rewrite setbn_setbn_same.
  pose proof Hb1 as (Hl & Ht & Hm & Hn & Hf & Hd).
  assert (Hlen1 : (1 <= length (bn_buf b1))%nat) by (unfold bdm in Hd1; lia).
  assert (Hds : bn_d b1 <> None). { intros E. apply Hd in E. rewrite E in Hlen1. cbn in Hlen1. lia. }
  assert (Hne : forall l : list Z, length l = length (bn_buf b1) -> l <> []). { intros l Hl0 E. subst l. cbn in Hl0. lia. }
  assert (Hl0 : (0 < length (bn_buf b1))%nat) by lia.
  apply HQ.
  - unfold bnv, bnw, bn_mag, bn_norm; cbn -[upd Z.eqb].
    destruct (Z.eqb_spec w 0) as [->|NE]; cbn -[upd].
    + rewrite upd_length by lia. split; [|left; reflexivity]. split; [apply upd_limbs; [exact Hl|unfold limb; lia]|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hf|].
      split; [intros E; exfalso; exact (Hds E)|intros E; exfalso; exact (Hne _ (upd_length (bn_buf b1) 0%nat 0 Hl0) E)].
    + rewrite upd_length by lia. split; [|right; cbn; rewrite nth_upd_same by lia; exact NE]. split; [apply upd_limbs; [exact Hl|unfold limb; lia]|]. split; [lia|]. split.
      { destruct (bn_buf b1) as [|x l] eqn:Eb; [cbn in Hlen1; lia|]. cbn -[BW]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity. }
      split; [reflexivity|]. split; [exact Hf|].
      split; [intros E; exfalso; exact (Hds E)|intros E; exfalso; exact (Hne _ (upd_length (bn_buf b1) 0%nat w Hl0) E)].
  - unfold bdm in *. cbn. rewrite upd_length by lia. lia.
  - cbn. destruct (w =? 0); lia.
  - unfold bnb in *. cbn -[Z.mul Z.of_nat]. rewrite upd_length by lia. exact HP1.
Qed.

Lemma Bp_is_pow n : Bp n = 2 ^ (64 * Z.of_nat n).
Proof. unfold Bp. rewrite BW_pow, <- Z.pow_mul_r by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma BN_lshift_bwp : forall r n (bs : ST) v L X0 X (Q : unit * ST -> list (ptr * Z) -> Prop),
  st2 bs -> (r < 2)%nat -> bnv (getbn r bs) v -> 0 <= n < 64 -> (Z.of_nat (bn_top (getbn r bs)) + 1 <= 512) -> roomy0 X0 ->
  Permutation X (bnb (getbn r bs) ++ L ++ X0) -> zlength L <= 6 -> bnonneg L -> bsum L + 8 * bdm (getbn r bs) + 8 * (Z.of_nat (bn_top (getbn r bs)) + 1) <= 16000 ->
  (forall b' X', bnv b' (v * 2 ^ n) -> bdm b' = Z.max (bdm (getbn r bs)) (Z.of_nat (bn_top (getbn r bs)) + 1) -> (bn_top b' <= bn_top (getbn r bs) + 1)%nat ->
                Permutation X' (bnb b' ++ L ++ X0) -> Q (tt, setbn r b' bs) X') ->
  bwp (BN_lshift ops r r n bs) X Q.
Proof.
  intros r n bs v L X0 X Q H2 Hr Hb Hn Htop HR HP HLc HLn Hsz HQ. pose proof Hb as ((Hl & Ht & Hm & Hneg & Hf & Hd) & Hnorm).
  unfold BN_lshift. destruct (Z.ltb_spec n 0); [lia|]. apply bwp_bbind.
  unfold bn_lshift_fixed_top. destruct (Z.ltb_spec n 0); [lia|].
  replace (Z.to_nat (n / 64)) with 0%nat by (rewrite Z.div_small by lia; reflexivity).
  apply bwp_bbind. cbn [bget ret tree_ops ApLogic.bwp fst snd]. rewrite Nat.add_0_r.
  apply bwp_bbind. eapply bn_wexpand_bwp; [exact H2|exact Hr|exact (bnv_w _ _ Hb)|rewrite Nat2Z.inj_add; cbn [Z.of_nat]; lia|exact HR|exact HP|exact HLc|exact HLn| |].
  { unfold bdm in *. rewrite Nat2Z.inj_add. cbn [Z.of_nat]. lia. }
  intros b1 X1 Hb1 _ Ht1 Hd1 Hf1 Esrc0 HP1.
  apply bwp_bbind. cbn [bget ret tree_ops ApLogic.bwp fst snd]. apply bwp_bbind. cbn [bget ret tree_ops ApLogic.bwp fst snd].
  rewrite !(getbn_setbn_same2 r b1 bs H2 Hr). cbn -[getbn setbn lshift_limbs splice upd firstn Z.modulo Nat.add Nat.eqb repeat app strip_top bn_correct_top_pure Z.mul Z.pow].
  rewrite !setbn_setbn_same.
  pose proof Hb1 as (Hl1 & Htt1 & Hm1 & Hneg1 & Hff1 & Hdd1).
  set (src := firstn (bn_top (getbn r bs)) (bn_buf (getbn r bs))) in *.
  assert (Esrc : firstn (bn_top b1) (bn_buf b1) = src) by exact Esrc0.
  assert (Hsrc : limbs src) by (unfold src; apply limbs_firstn; exact Hl).
  assert (Hsl : length src = bn_top (getbn r bs)) by (unfold src; apply firstn_length_le; exact Ht).
  assert (Hlb : 0 <= n mod 64 < 64) by (apply Z.mod_pos_bound; lia). rewrite (Z.mod_small n 64) in * by lia.
  pose proof (lshift_limbs_spec src n 0 Hsrc ltac:(lia) ltac:(split; [lia|apply Z.pow_pos_nonneg; lia])) as Hls.
  rewrite (getbn_setbn_same2 r _ bs H2 Hr). rewrite ?setbn_setbn_same. cbn [Nat.eqb]. rewrite Esrc, Ht1. rewrite !Nat.add_0_r.
  destruct (lshift_limbs src n 0) as [ls mo] eqn:Els. destruct Hls as (L1 & L2 & L3 & L4).
  set (seg := ls ++ [mo]).
  assert (Hseg : limbs seg).
  { apply limbs_app; [exact L1|]. constructor; [|constructor]. unfold limb. rewrite BW_pow. split; [lia|]. eapply Z.lt_trans; [apply L3|]. apply Z.pow_lt_mono_r; lia. }
  assert (Hsegl : length seg = (bn_top (getbn r bs) + 1)%nat) by (unfold seg; rewrite length_app; cbn [length]; lia).
  set (buf0 := if (bn_top (getbn r bs) =? 0)%nat then upd (bn_buf b1) 0 0 else splice (bn_buf b1) 0 seg).
  assert (Ebuf0 : buf0 = splice (bn_buf b1) 0 seg).
  { unfold buf0. destruct (Nat.eqb_spec (bn_top (getbn r bs)) 0) as [E0|E0]; [|reflexivity].
    unfold seg. assert (Es : src = []) by (destruct src; [reflexivity|cbn in Hsl; lia]). rewrite Es in Els. cbn [lshift_limbs] in Els. injection Els as <- <-. reflexivity. }
  fold buf0. rewrite Ebuf0. clear buf0 Ebuf0.
  assert (Hfit : (0 + length seg <= length (bn_buf b1))%nat) by (unfold bdm in Hd1; rewrite Hsegl; lia).
  set (b2 := bn_correct_top_pure _).
  assert (Hval : lval (firstn (bn_top (getbn r bs) + 1) (splice (bn_buf b1) 0 seg)) = v * 2 ^ n).
  { rewrite <- Hsegl. rewrite firstn_splice_0 by (first [reflexivity|lia]). unfold seg. rewrite lval_app, L2, Hsl. cbn [lval]. rewrite Z.mul_0_r, Z.add_0_r.
    unfold bn_mag in Hm. fold src in Hm. rewrite <- Hm. rewrite <- Hsl. lia. }
  pose proof (strip_top_spec (splice (bn_buf b1) 0 seg) (bn_top (getbn r bs) + 1) ltac:(rewrite splice_length by exact Hfit; lia)) as (S1 & S2 & S3).
  assert (Hb2 : bnv b2 (v * 2 ^ n)).
  { unfold b2, bnv, bnw, bn_correct_top_pure, bn_mag, bn_norm; cbn -[splice strip_top Nat.add Z.mul Z.pow]. split; [|exact S3].
    split; [apply splice_limbs; [exact Hl1|exact Hseg]|]. split. { rewrite splice_length by exact Hfit. lia. }
    split; [rewrite S2; exact Hval|]. split; [destruct (strip_top _ _ =? 0)%nat; [reflexivity|exact Hneg1]|]. split; [exact Hff1|].
    split; [intros E; apply Hdd1 in E; apply (f_equal (@length Z)) in E; cbn in E; exfalso; lia|].
    intros E. apply (f_equal (@length Z)) in E. rewrite splice_length in E by exact Hfit. cbn in E. exfalso; lia. }
  apply HQ; [exact Hb2| | |].
  - unfold b2, bdm, bn_correct_top_pure; cbn -[splice Z.of_nat Z.max Z.add]. rewrite splice_length by exact Hfit. unfold bdm in Hd1. rewrite Hd1. rewrite Nat2Z.inj_add. cbn [Z.of_nat]. lia.
  - unfold b2, bn_correct_top_pure; cbn -[strip_top Nat.add]. exact S1.
  - unfold bnb, b2, bn_correct_top_pure; cbn -[splice Z.of_nat Z.mul app]. rewrite splice_length by exact Hfit. unfold bnb in HP1. exact HP1.
Qed.

Lemma bnv_okv (b : BN) v : bnw b v -> bg_okv b.
Proof. intros (Hl & Ht & _). split; assumption. Qed.
End BnSpec.

Section BnSpec2.
Context {ptr : Type}.
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ST := (bstate ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).
Local Notation okA := (okAp (ptr:=ptr) AP_NB AP_TOT) (only parsing).
Local Notation bwp := (bwp (okAp (ptr:=ptr) AP_NB AP_TOT)) (only parsing).

Lemma BN_add_word_bwp : forall r w (bs : ST) v L X0 X (Q : unit * ST -> list (ptr * Z) -> Prop),
  st2 bs -> (r < 2)%nat -> bnv (getbn r bs) v -> 0 <= w < BW -> (Z.of_nat (bn_top (getbn r bs)) + 1 <= 512) -> roomy0 X0 ->
  Permutation X (bnb (getbn r bs) ++ L ++ X0) -> zlength L <= 6 -> bnonneg L -> bsum L + 8 * bdm (getbn r bs) + 8 * (Z.of_nat (bn_top (getbn r bs)) + 1) <= 16000 ->
  (forall b' X', bnv b' (v + w) -> bdm b' <= Z.max (bdm (getbn r bs)) (Z.of_nat (bn_top (getbn r bs)) + 1) -> (bn_top b' <= bn_top (getbn r bs) + 1)%nat ->
                Permutation X' (bnb b' ++ L ++ X0) -> Q (tt, setbn r b' bs) X') ->
  bwp (BN_add_word ops r w bs) X Q.
Proof.
  intros r w bs v L X0 X Q H2 Hr Hb Hw Htop HR HP HLc HLn Hsz HQ. pose proof Hb as ((Hl & Ht & Hm & Hneg & Hf & Hd) & Hnorm).
  unfold BN_add_word. destruct (Z.eqb_spec w 0) as [->|Hw0].
  { cbn. pose proof (HQ (getbn r bs) X) as HQ'. rewrite setbn_getbn_id in HQ'. rewrite Z.add_0_r in HQ'. apply HQ'; [exact Hb|lia|lia|exact HP]. }
  apply bwp_bbind. cbn [bget ret tree_ops ApLogic.bwp fst snd].
  destruct (Nat.eqb_spec (bn_top (getbn r bs)) 0) as [Et|Et].
  { pose proof (proj1 (bnv_zero_iff _ _ Hb) Et) as ->. rewrite Z.add_0_l in HQ.
    eapply BN_set_word_bwp; [exact H2|exact Hr|exact (bnv_w _ _ Hb)|exact Hw|exact HR|exact HP|exact HLc|exact HLn|lia|].
    intros b' X' Hb' Hd' Ht' HP'. apply HQ; [exact Hb'|lia|lia|exact HP']. }
  rewrite Hneg.
  set (a := getbn r bs) in *.
  set (src := firstn (bn_top a) (bn_buf a)) in *.
  assert (Hsrc : limbs src) by (unfold src; apply limbs_firstn; exact Hl).
  assert (Hsl : length src = bn_top a) by (unfold src; apply firstn_length_le; exact Ht).
  pose proof (add_word_limbs_spec src w Hsrc Hw) as Hp. destruct (add_word_limbs src w) as [l w'] eqn:El.
  destruct Hp as (P1 & P2 & P3 & P4 & P5). rewrite Hsl in P2, P5.
  assert (Hne : src <> []) by (intros E; rewrite E in Hsl; cbn in Hsl; lia). specialize (P4 Hne).
  assert (Hlen1 : length (splice (bn_buf a) 0 l) = length (bn_buf a)) by (apply splice_length; lia).
  assert (Hf1 : firstn (bn_top a) (splice (bn_buf a) 0 l) = l) by (apply firstn_splice_0; [exact P2|lia]).
  assert (Hmag_a : v = lval src) by (unfold bn_mag in Hm; symmetry; exact Hm).
  apply bwp_bbind. cbn [bset ret tree_ops ApLogic.bwp fst snd].
  set (b1 := bn_with_buf a (splice (bn_buf a) 0 l)).
  assert (Hb1w : bnw b1 (v + w - Bp (bn_top a) * w')).
  { unfold b1, bnw, bn_with_buf, bn_mag; cbn -[splice]. rewrite Hf1, Hlen1. split; [apply splice_limbs; assumption|]. split; [exact Ht|]. split; [lia|].
    split; [exact Hneg|]. split; [exact Hf|]. split; [intros E; apply Hd in E; apply (f_equal (@length Z)) in E; cbn in E|intros E; apply (f_equal (@length Z)) in E; rewrite Hlen1 in E; cbn in E]; exfalso; lia. }
  pose proof (bnv_bounds _ _ Hb) as [HB1 HB2]. specialize (HB2 ltac:(lia)). pose proof (lval_bound l P1) as HlB. rewrite P2 in HlB.
  destruct (Z.eqb_spec w' 0) as [Ew|Ew].
  - cbn. rewrite Ew, Z.mul_0_r, Z.sub_0_r in Hb1w. apply HQ.
    + split; [exact Hb1w|]. apply norm_of_mag_ge; [apply (bnv_okv _ _ Hb1w)|]. right. destruct Hb1w as (_ & _ & -> & _). unfold b1, bn_with_buf; cbn. lia.
    + unfold bdm, b1, bn_with_buf in *; cbn -[splice Z.of_nat Z.max] in *. rewrite Hlen1. lia.
    + unfold b1, bn_with_buf; cbn. lia.
    + unfold bnb, b1, bn_with_buf in *; cbn -[splice Z.of_nat Z.mul app] in *. rewrite Hlen1. exact HP.
  - assert (Ew1 : w' = 1) by lia.
    apply bwp_bbind. rewrite <- (getbn_setbn_same2 r b1 bs H2 Hr) in Hb1w.
    eapply bn_wexpand_bwp; [apply st2_setbn; exact H2|exact Hr|exact Hb1w| |exact HR| | exact HLc|exact HLn| |]. { rewrite Nat2Z.inj_add. cbn [Z.of_nat]. lia. } 
    { rewrite ?(getbn_setbn_same2 r b1 bs H2 Hr). unfold bnb, b1, bn_with_buf in *; cbn -[splice Z.of_nat Z.mul app] in *. rewrite Hlen1. exact HP. }
    { rewrite ?(getbn_setbn_same2 r b1 bs H2 Hr). unfold bdm, b1, bn_with_buf in *; cbn -[splice Z.of_nat Z.mul Z.add] in *. rewrite ?Hlen1. lia. }
    rewrite ?(getbn_setbn_same2 r b1 bs H2 Hr). rewrite (getbn_setbn_same2 r b1 bs H2 Hr) in Hb1w. intros b2 X2 Hb2 _ Ht2 Hd2 Hf2 Hpre HP2.
    apply bwp_bbind. cbn [bget ret tree_ops ApLogic.bwp fst snd]. rewrite setbn_setbn_same, (getbn_setbn_same2 r b2 bs H2 Hr).
    cbn [bset ret tree_ops ApLogic.bwp fst snd]. rewrite setbn_setbn_same.
    pose proof Hb2 as (Hl2 & Htt2 & Hm2 & Hneg2 & Hff2 & Hdd2).
    unfold b1, bn_with_buf in Ht2, Hd2, Hpre; cbn -[splice Z.of_nat Z.max Z.add] in Ht2, Hd2, Hpre. rewrite ?Hf1 in Hpre. unfold bdm in Hd2; cbn -[splice Z.of_nat Z.max Nat.add] in Hd2. rewrite ?Hlen1 in Hd2.
    assert (Hlen2b : (bn_top a + 1 <= length (bn_buf b2))%nat) by (unfold bdm in Hd2; lia).
    assert (Hlen2 : length (upd (bn_buf b2) (bn_top a) w') = length (bn_buf b2)) by (apply upd_length; lia).
    assert (Hfst : firstn (bn_top a + 1) (upd (bn_buf b2) (bn_top a) w') = l ++ [w']).
    { rewrite <- Hpre, Ht2. apply firstn_upd_last. lia. }
    assert (Hb3w : bnw (mkBN (bn_d b2) (upd (bn_buf b2) (bn_top a) w') (bn_top a + 1) (bn_neg b2) (bn_flags b2)) (v + w)).
    { unfold bnw, bn_mag; cbn -[upd Nat.add]. rewrite Hfst, Hlen2, lval_app, P2. cbn [lval].
      split; [apply upd_limbs; [exact Hl2|unfold limb; lia]|]. split; [lia|]. split; [lia|]. split; [exact Hneg2|]. split; [exact Hff2|].
      split; [intros E; apply Hdd2 in E; apply (f_equal (@length Z)) in E; cbn in E|intros E; apply (f_equal (@length Z)) in E; rewrite Hlen2 in E; cbn in E]; exfalso; lia. }
    apply HQ.
    + split; [exact Hb3w|]. unfold bn_norm; cbn -[upd Nat.add]. right. replace (bn_top a + 1 - 1)%nat with (bn_top a) by lia. rewrite nth_upd_same by lia. lia.
    + unfold bdm in *; cbn. rewrite Hlen2. lia.
    + cbn. lia.
    + unfold bnb in *; cbn -[Z.of_nat Z.mul app upd] in *. rewrite Hlen2. exact HP2.
Qed.


Lemma lval_firstn_S : forall (l : list Z) t, (S t <= length l)%nat -> lval (firstn (S t) l) = lval (firstn t l) + Bp t * nth t l 0.
Proof.
  intros l t Ht. rewrite (lval_split_le t (firstn (S t) l)) by (rewrite firstn_length_le; lia).
  rewrite firstn_firstn, Nat.min_l by lia. rewrite skipn_firstn_one by exact Ht. cbn [lval]. lia.
Qed.

Lemma BN_sub_word_bwp : forall r w (bs : ST) v X (Q : unit * ST -> list (ptr * Z) -> Prop),
  st2 bs -> (r < 2)%nat -> bnv (getbn r bs) v -> 0 < w < BW -> w <= v ->
  (forall b', bnv b' (v - w) -> bdm b' = bdm (getbn r bs) -> (bn_top b' <= bn_top (getbn r bs))%nat -> bnb b' = bnb (getbn r bs) -> Q (tt, setbn r b' bs) X) ->
  bwp (BN_sub_word ops r w bs) X Q.
Proof.
  intros r w bs v X Q H2 Hr Hb Hw Hwv HQ. pose proof Hb as ((Hl & Ht & Hm & Hneg & Hf & Hd) & Hnorm).
  pose proof (bnv_bounds _ _ Hb) as [HB1 HB2].
  unfold BN_sub_word. destruct (Z.eqb_spec w 0) as [->|Hw0]; [lia|].
  apply bwp_bbind. cbn [bget ret tree_ops ApLogic.bwp fst snd].
  set (a := getbn r bs) in *.
  destruct (Nat.eqb_spec (bn_top a) 0) as [Et|Et].
  { exfalso. rewrite Et in HB1. rewrite Bp_0 in HB1. lia. }
  specialize (HB2 ltac:(lia)). rewrite Hneg.
  set (src := firstn (bn_top a) (bn_buf a)) in *.
  assert (Hsrc : limbs src) by (unfold src; apply limbs_firstn; exact Hl).
  assert (Hsl : length src = bn_top a) by (unfold src; apply firstn_length_le; exact Ht).
  assert (Hmag_a : v = lval src) by (unfold bn_mag in Hm; symmetry; exact Hm).
  assert (Hc1 : (bn_top a =? 1)%nat && (nth 0 (bn_buf a) 0 <? w) = false).
  { destruct (Nat.eqb_spec (bn_top a) 1) as [E1|E1]; [|reflexivity]. cbn [andb]. apply Z.ltb_ge.
    rewrite Hmag_a in Hwv. unfold src in Hwv. rewrite E1 in Hwv. destruct (bn_buf a) as [|x tl] eqn:Eb; [exfalso; rewrite E1 in Ht; cbn in Ht; lia|]. cbn in Hwv. cbn. rewrite Z.mul_0_r, Z.add_0_r in Hwv. exact Hwv. }
  rewrite Hc1.
  pose proof (sub_word_limbs_spec src w 0 Hsrc ltac:(lia) ltac:(lia)) as Hp. destruct (sub_word_limbs src w 0) as [l i] eqn:El.
  destruct Hp as (P1 & P2 & P3 & P4 & P5 & P6). rewrite Hsl in P2, P5.
  assert (Hne : src <> []) by (intros E; rewrite E in Hsl; cbn in Hsl; lia). specialize (P5 Hne). rewrite Nat.sub_0_r in P6.
  assert (Hlen1 : length (splice (bn_buf a) 0 l) = length (bn_buf a)) by (apply splice_length; lia).
  assert (Hf1 : firstn (bn_top a) (splice (bn_buf a) 0 l) = l) by (apply firstn_splice_0; [exact P2|lia]).
  assert (Hnthl : forall j, (j < bn_top a)%nat -> nth j (splice (bn_buf a) 0 l) 0 = nth j l 0).
  { intros j Hj. rewrite <- (Nat.add_0_l j) at 1. apply nth_splice_same; lia. }
  cbn [bset ret tree_ops ApLogic.bwp fst snd].
  set (top' := if (nth i (splice (bn_buf a) 0 l) 0 =? 0) && (i =? bn_top a - 1)%nat then (bn_top a - 1)%nat else bn_top a).
  assert (Htop' : (top' = (bn_top a - 1)%nat /\ i = (bn_top a - 1)%nat /\ nth i l 0 = 0) \/ (top' = bn_top a /\ nth (bn_top a - 1) l 0 <> 0)).
  { unfold top'. rewrite Hnthl by lia. destruct (Z.eqb_spec (nth i l 0) 0) as [Ez|Ez]; destruct (Nat.eqb_spec i (bn_top a - 1)) as [Ei|Ei]; cbn [andb].
    - left. repeat split; assumption.
    - right. split; [reflexivity|]. rewrite P6 by lia. destruct Hnorm as [E0|Hnz]; [lia|]. unfold src. rewrite nth_firstn. destruct (Nat.ltb_spec (bn_top a - 1) (bn_top a)); [exact Hnz|lia].
    - right. split; [reflexivity|]. rewrite <- Ei. exact Ez.
    - right. split; [reflexivity|]. rewrite P6 by lia. destruct Hnorm as [E0|Hnz]; [lia|]. unfold src. rewrite nth_firstn. destruct (Nat.ltb_spec (bn_top a - 1) (bn_top a)); [exact Hnz|lia]. }
  assert (HlS : lval l = lval (firstn (bn_top a - 1) l) + Bp (bn_top a - 1) * nth (bn_top a - 1) l 0).
  { rewrite <- (firstn_all2 l (n:=bn_top a)) at 1 by lia. replace (bn_top a) with (S (bn_top a - 1)) at 1 by lia. apply lval_firstn_S. lia. }
  apply HQ.
  - unfold bnv, bnw, bn_mag, bn_norm; cbn -[splice top' Z.sub]. fold top'. rewrite Hlen1.
    assert (Hmag' : lval (firstn top' (splice (bn_buf a) 0 l)) = v - w /\ (top' = 0%nat \/ nth (top' - 1) (splice (bn_buf a) 0 l) 0 <> 0)).
    { destruct Htop' as [(E1 & E2 & E3)|(E1 & E2)]; rewrite E1.
      + replace (firstn (bn_top a - 1) (splice (bn_buf a) 0 l)) with (firstn (bn_top a - 1) (firstn (bn_top a) (splice (bn_buf a) 0 l)))
          by (rewrite firstn_firstn; f_equal; lia).
        rewrite Hf1. rewrite E2 in E3. rewrite E3, Z.mul_0_r, Z.add_0_r in HlS. split; [lia|].
        destruct (Nat.eq_dec (bn_top a - 1) 0) as [E0|E0]; [left; exact E0|right]. rewrite Hnthl by lia. intros Ez.
        pose proof (lval_firstn_S l (bn_top a - 1 - 1) ltac:(lia)) as HlS2. replace (S (bn_top a - 1 - 1)) with (bn_top a - 1)%nat in HlS2 by lia.
        rewrite Ez, Z.mul_0_r, Z.add_0_r in HlS2.
        pose proof (lval_bound (firstn (bn_top a - 1 - 1) l) (limbs_firstn _ _ P1)) as HB3. rewrite firstn_length_le in HB3 by lia.
        pose proof (Bp_S (bn_top a - 1 - 1)) as HBS. replace (S (bn_top a - 1 - 1)) with (bn_top a - 1)%nat in HBS by lia.
        pose proof (Bp_pos (bn_top a - 1 - 1)). pose proof BW_pos. nia.
      + rewrite Hf1. split; [lia|]. right. rewrite Hnthl by lia. exact E2. }
    destruct Hmag' as [M1 M2].
    split; [|exact M2]. split; [apply splice_limbs; assumption|]. split; [unfold top'; destruct (_ && _); lia|]. split; [exact M1|]. split; [reflexivity|]. split; [exact Hf|].
    split; [intros E; apply Hd in E; apply (f_equal (@length Z)) in E; cbn in E|intros E; apply (f_equal (@length Z)) in E; rewrite Hlen1 in E; cbn in E]; exfalso; lia.
  - unfold bdm; cbn -[splice Z.of_nat]. rewrite Hlen1. reflexivity.
  - cbn -[top']. unfold top'; destruct (_ && _); lia.
  - unfold bnb; cbn -[splice Z.of_nat Z.mul]. rewrite Hlen1. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma BN_dup_bwp : forall rt ra (bs : ST) v L X0 X (Q : ptr * ST -> list (ptr * Z) -> Prop),
  st2 bs -> (rt < 2)%nat -> (ra < 2)%nat -> rt <> ra -> bnv (getbn ra bs) v -> Z.of_nat (bn_top (getbn ra bs)) <= 512 -> roomy0 X0 ->
  Permutation X (L ++ X0) -> zlength L <= 5 -> bnonneg L -> bsum L + 24 + 8 * Z.of_nat (bn_top (getbn ra bs)) <= 16000 ->
  (forall p b' X', bnv b' v -> bdm b' = Z.of_nat (bn_top (getbn ra bs)) -> bn_top b' = bn_top (getbn ra bs) ->
      Permutation X' (bnb b' ++ ((p, 24) :: L) ++ X0) -> Q (p, setbn rt b' bs) X') ->
  bwp (BN_dup ops rt ra bs) X Q.
Proof.
  intros rt ra bs v L X0 X Q H2 Hrt Hra Hne Hb Htop HR HP HLc HLn Hsz HQ. pose proof Hb as ((Hl & Ht & Hm & Hneg & Hf & Hd) & Hnorm).
  unfold BN_dup. apply bwp_bbind. eapply BN_new_bwp; [exact H2|exact Hrt|exact HR|exact HP|lia|exact HLn|lia|].
  intros p X1 HP1. cbn [fst snd]. apply bwp_bbind. unfold BN_copy. apply bwp_bbind. cbn [bget ret tree_ops ApLogic.bwp fst snd].
  rewrite (getbn_setbn_other2 rt ra _ bs Hne). unfold has_flag. rewrite Hf. cbn -[bn_wexpand getbn setbn splice firstn bbind Nat.ltb].
  destruct (Nat.eqb_spec rt ra) as [E|_]; [exfalso; exact (Hne E)|].
  apply bwp_bbind.
  assert (Hnilw : bnw (getbn rt (setbn rt (bn_nil BN_FLG_MALLOCED) bs)) 0).
  { rewrite (getbn_setbn_same2 rt _ bs H2 Hrt). exact (bnv_w _ _ bnv_nil). }
  eapply (bn_wexpand_bwp rt (bn_top (getbn ra bs)) _ 0 ((p, 24) :: L) X0 X1);
    [apply st2_setbn; exact H2|exact Hrt|exact Hnilw|exact Htop|exact HR| |change ((p, 24) :: L) with ([(p, 24)] ++ L); rewrite zlen_app'; replace (zlength [(p, 24)]) with 1 by reflexivity; lia|apply Forall_cons; [cbn; lia|exact HLn]| |].
  { rewrite (getbn_setbn_same2 rt _ bs H2 Hrt). cbn. exact HP1. }
  { rewrite (getbn_setbn_same2 rt _ bs H2 Hrt). unfold bdm; cbn -[Z.of_nat Z.mul Z.add bsum]. change ((p, 24) :: L) with ([(p, 24)] ++ L). rewrite bsum_app. replace (bsum [(p, 24)]) with 24 by reflexivity. lia. }
  rewrite (getbn_setbn_same2 rt _ bs H2 Hrt). intros b1 X2 Hb1 _ Ht1 Hd1 Hf1 _ HP2. cbn [fst snd].
  apply bwp_bbind. cbn [bget ret tree_ops ApLogic.bwp fst snd]. rewrite setbn_setbn_same, (getbn_setbn_same2 rt _ bs H2 Hrt).
  cbn [bset ret tree_ops ApLogic.bwp fst snd]. rewrite ?setbn_setbn_same. cbn [bret ret tree_ops ApLogic.bwp fst snd]. rewrite ?setbn_setbn_same. 
  pose proof Hb1 as (Hl1 & Htt1 & Hm1 & Hneg1 & Hff1 & Hdd1). cbn [bn_nil bn_top bn_flags] in Ht1, Hf1, Hd1. unfold bdm in Hd1; cbn [bn_nil bn_buf length Z.of_nat Z.max] in Hd1.
  rewrite Z.max_r in Hd1 by lia.
  set (a := getbn ra bs) in *. set (src := firstn (bn_top a) (bn_buf a)) in *.
  assert (Hsrc : limbs src) by (unfold src; apply limbs_firstn; exact Hl).
  assert (Hsl : length src = bn_top a) by (unfold src; apply firstn_length_le; exact Ht).
  set (buf := if (0 <? bn_top a)%nat then splice (bn_buf b1) 0 src else bn_buf b1).
  assert (Hbuf : length buf = length (bn_buf b1) /\ limbs buf /\ firstn (bn_top a) buf = src).
  { unfold buf. destruct (Nat.ltb_spec 0 (bn_top a)) as [Hp0|Hp0].
    - split; [apply splice_length; rewrite Hsl; lia|]. split; [apply splice_limbs; assumption|]. apply firstn_splice_0; [exact Hsl|lia].
    - split; [reflexivity|]. split; [exact Hl1|]. replace (bn_top a) with 0%nat by lia. unfold src. replace (bn_top a) with 0%nat by lia. reflexivity. }
  destruct Hbuf as (B1 & B2 & B3).
  apply HQ.
  - unfold bnv, bnw, bn_mag, bn_norm; cbn -[buf]. rewrite B1, B3. split. 
    + split; [exact B2|]. split; [lia|]. split; [unfold bn_mag in Hm; exact Hm|]. split; [exact Hneg|]. split; [exact Hff1|].
      split; [intros E; apply Hdd1 in E; apply (f_equal (@length Z)) in E; cbn in E|intros E; apply (f_equal (@length Z)) in E; rewrite B1 in E; cbn in E].
      * destruct buf; [reflexivity|cbn in B1; exfalso; lia].
      * destruct Hdd1 as [_ Hx]. apply Hx. destruct (bn_buf b1); [reflexivity|cbn in E; lia].
    + destruct (Nat.eq_dec (bn_top a) 0) as [E0|E0]; [left; exact E0|right]. destruct Hnorm as [E1|Hnz]; [lia|].
      intros Ez. apply Hnz.
      assert (E1 : nth (bn_top a - 1) buf 0 = nth (bn_top a - 1) (firstn (bn_top a) buf) 0).
      { rewrite nth_firstn. destruct (Nat.ltb_spec (bn_top a - 1) (bn_top a)); [reflexivity|lia]. }
      assert (E2 : nth (bn_top a - 1) (bn_buf a) 0 = nth (bn_top a - 1) src 0).
      { unfold src. rewrite nth_firstn. destruct (Nat.ltb_spec (bn_top a - 1) (bn_top a)); [reflexivity|lia]. }
      rewrite E2, <- B3, <- E1. exact Ez.
  - unfold bdm; cbn -[buf Z.of_nat]. rewrite B1. lia.
  - reflexivity.
  - unfold bnb; cbn -[buf Z.of_nat Z.mul app]. rewrite B1. unfold bnb in HP2. exact HP2.
Qed.

Lemma firstn_upd_below : forall (buf : list Z) i d n, (n <= i)%nat -> (i < length buf)%nat -> firstn n (upd buf i d) = firstn n buf.
Proof. intros buf i d n Hn Hi. unfold upd. apply firstn_splice_below; lia. Qed.

Lemma subw_mulw_rem : forall ret l d w, 0 < w < BW -> 0 <= l < BW -> 0 <= ret ->
  d = (ret * BW + l) / w -> subw l (mulw d w) = (ret * BW + l) mod w.
Proof.
  intros ret l d w Hw Hl Hret Hd. pose proof BW_pos as HB.
  pose proof (Z.div_mod (ret * BW + l) w ltac:(lia)) as E. rewrite <- Hd in E.
  pose proof (Z.mod_pos_bound (ret * BW + l) w ltac:(lia)) as M.
  unfold subw, mulw. rewrite Zminus_mod_idemp_r.
  replace (l - d * w) with ((ret * BW + l) mod w + (- ret) * BW) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma div_word_loop_spec : forall i buf w ret, limbs buf -> (i <= length buf)%nat -> 2^63 <= w < BW -> 0 <= ret < w ->
  let '(buf', ret') := div_word_loop i buf w ret in
  limbs buf' /\ length buf' = length buf /\ (forall j, (i <= j)%nat -> nth j buf' 0 = nth j buf 0) /\
  lval (firstn i buf') * w + ret' = ret * Bp i + lval (firstn i buf) /\ 0 <= ret' < w.
Proof.
  induction i as [|i IH]; intros buf w ret Hl Hi Hw Hret.
  - cbn [div_word_loop]. rewrite Bp_0. cbn [firstn lval]. split; [exact Hl|]. split; [reflexivity|]. split; [intros; reflexivity|]. change (firstn 0 buf) with (@nil Z). cbn [lval]. lia.
  - cbn [div_word_loop]. pose proof BW_pos as HB. assert (HP63 : 0 < 2 ^ 63) by (apply Z.pow_pos_nonneg; lia).
    set (l := nth i buf 0). set (d := div_words ret l w). set (ret1 := subw l (mulw d w)).
    pose proof (limbs_nth buf i Hl) as Hlb. fold l in Hlb. unfold limb in Hlb.
    assert (Hd : d = (ret * BW + l) / w) by (unfold d; apply div_words_correct; lia).
    pose proof (Z.div_mod (ret * BW + l) w ltac:(lia)) as E. rewrite <- Hd in E.
    pose proof (Z.mod_pos_bound (ret * BW + l) w ltac:(lia)) as M.
    assert (Hr1 : ret1 = (ret * BW + l) mod w). { unfold ret1; apply (subw_mulw_rem ret); lia. }
    assert (Hdb : 0 <= d < BW).
    { rewrite Hd. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
    assert (Hul : limbs (upd buf i d)) by (apply upd_limbs; [exact Hl|unfold limb; lia]).
    assert (Hui : (i <= length (upd buf i d))%nat) by (rewrite upd_length by lia; lia).
    specialize (IH (upd buf i d) w ret1 Hul Hui Hw ltac:(lia)).
    destruct (div_word_loop i (upd buf i d) w ret1) as [buf' ret']. destruct IH as (Q1 & Q2 & Q3 & Q4 & Q5).
    rewrite upd_length in Q2 by lia.
    split; [exact Q1|]. split; [exact Q2|]. split.
    { intros j Hj. rewrite Q3 by lia. apply nth_upd_other; lia. }
    split; [|exact Q5].
    rewrite !lval_firstn_S by lia. rewrite (Q3 i) by lia. rewrite nth_upd_same by lia. rewrite firstn_upd_below in Q4 by lia.
    rewrite Bp_S. fold l. nia.
Qed.

Lemma Bp_mono : forall n m, (n <= m)%nat -> Bp n <= Bp m.
Proof.
  intros n m H. replace m with (n + (m - n))%nat by lia. rewrite Bp_add. pose proof (Bp_pos n). pose proof (Bp_pos (m - n)). nia.
Qed.

Lemma bnv_top_le (b : BN) v k : bnv b v -> v < Bp k -> (bn_top b <= k)%nat.
Proof.
  intros Hb Hv. pose proof (bnv_bounds _ _ Hb) as [B1 B2]. destruct (Nat.le_gt_cases (bn_top b) k) as [H|H]; [exact H|].
  exfalso. specialize (B2 ltac:(lia)). pose proof (Bp_mono k (bn_top b - 1) ltac:(lia)). lia.
Qed.

Lemma DEC_facts : Z.land BN_DEC_CONV (BW - 1) = BN_DEC_CONV /\ (BN_DEC_CONV =? 0) = false /\ 64 - num_bits_word BN_DEC_CONV = 0
  /\ shlw BN_DEC_CONV 0 = BN_DEC_CONV /\ 2 ^ 63 <= BN_DEC_CONV < BW.
Proof. unfold BN_DEC_CONV. rewrite BW_pow. repeat split; try (vm_compute; reflexivity); vm_compute; discriminate. Qed.

Lemma BN_div_word_bwp : forall r (bs : ST) v L X0 X (Q : Z * ST -> list (ptr * Z) -> Prop),
  st2 bs -> (r < 2)%nat -> bnv (getbn r bs) v -> (Z.of_nat (bn_top (getbn r bs)) + 1 <= 512) -> roomy0 X0 ->
  Permutation X (bnb (getbn r bs) ++ L ++ X0) -> zlength L <= 6 -> bnonneg L -> bsum L + 8 * bdm (getbn r bs) + 8 * (Z.of_nat (bn_top (getbn r bs)) + 1) <= 16000 ->
  (forall b' X', bnv b' (v / BN_DEC_CONV) -> bdm b' <= Z.max (bdm (getbn r bs)) (Z.of_nat (bn_top (getbn r bs)) + 1) -> (bn_top b' <= bn_top (getbn r bs) + 1)%nat ->
                Permutation X' (bnb b' ++ L ++ X0) -> Q (v mod BN_DEC_CONV, setbn r b' bs) X') ->
  bwp (BN_div_word ops r BN_DEC_CONV bs) X Q.
Proof.
  intros r bs v L X0 X Q H2 Hr Hb Htop HR HP HLc HLn Hsz HQ. pose proof Hb as ((Hl & Ht & Hm & Hneg & Hf & Hd) & Hnorm).
  destruct DEC_facts as (D1 & D2 & D3 & D4 & D5). pose proof BW_pos as HB.
  unfold BN_div_word. rewrite D1, D2. apply bwp_bbind. cbn [bget ret tree_ops ApLogic.bwp fst snd].
  destruct (Nat.eqb_spec (bn_top (getbn r bs)) 0) as [Et|Et].
  { pose proof (proj1 (bnv_zero_iff _ _ Hb) Et) as ->. cbn. pose proof (HQ (getbn r bs) X) as HQ'. rewrite setbn_getbn_id in HQ'.
    rewrite Z.div_0_l, Z.mod_0_l in HQ' by (unfold BN_DEC_CONV; lia). apply HQ'; [exact Hb|lia|lia|exact HP]. }
  rewrite D3, D4. apply bwp_bbind.
  eapply BN_lshift_bwp; [exact H2|exact Hr|exact Hb|lia|exact Htop|exact HR|exact HP|exact HLc|exact HLn|exact Hsz|].
  intros b1 X1 Hb1 Hd1 Ht1 HP1. cbn [fst snd]. rewrite Z.pow_0_r, Z.mul_1_r in Hb1.
  apply bwp_bbind. cbn [bget ret tree_ops ApLogic.bwp fst snd]. rewrite (getbn_setbn_same2 r b1 bs H2 Hr).
  pose proof Hb1 as ((Hl1 & Htt1 & Hm1 & Hneg1 & Hff1 & Hdd1) & Hnorm1).
  pose proof (div_word_loop_spec (bn_top b1) (bn_buf b1) BN_DEC_CONV 0 Hl1 Htt1 D5 ltac:(lia)) as HL.
  destruct (div_word_loop (bn_top b1) (bn_buf b1) BN_DEC_CONV 0) as [buf' ret']. destruct HL as (Q1 & Q2 & Q3 & Q4 & Q5).
  rewrite Z.mul_0_l, Z.add_0_l in Q4. unfold bn_mag in Hm1. rewrite Hm1 in Q4.
  set (q := lval (firstn (bn_top b1) buf')) in *.
  assert (Hq : q = v / BN_DEC_CONV) by (apply (Z.div_unique _ _ _ ret'); lia).
  assert (Hrm : ret' = v mod BN_DEC_CONV) by (apply (Z.mod_unique _ _ q); lia).
  apply bwp_bbind. cbn [bset ret tree_ops ApLogic.bwp fst snd]. rewrite setbn_setbn_same. cbn [bret ret tree_ops ApLogic.bwp fst snd].
  unfold shrw. rewrite Z.pow_0_r, Z.div_1_r. rewrite Hrm.
  pose proof (bnv_bounds _ _ Hb1) as [HB1 HB2].
  set (top' := if (0 <? bn_top b1)%nat && (nth (bn_top b1 - 1) buf' 0 =? 0) then (bn_top b1 - 1)%nat else bn_top b1).
  assert (Htop' : (top' = (bn_top b1 - 1)%nat /\ (0 < bn_top b1)%nat /\ nth (bn_top b1 - 1) buf' 0 = 0) \/ (top' = bn_top b1 /\ (bn_top b1 = 0%nat \/ nth (bn_top b1 - 1) buf' 0 <> 0))).
  { unfold top'. destruct (Nat.ltb_spec 0 (bn_top b1)) as [E1|E1]; destruct (Z.eqb_spec (nth (bn_top b1 - 1) buf' 0) 0) as [E2|E2]; cbn [andb]; [left; repeat split; assumption|right..]; split; try reflexivity; [right; exact E2|left; lia|left; lia]. }
  assert (Hmag' : lval (firstn top' buf') = q /\ (top' = 0%nat \/ nth (top' - 1) buf' 0 <> 0)).
  { destruct Htop' as [(E1 & E2 & E3)|(E1 & E2)]; rewrite E1; [|split; [reflexivity|exact E2]].
    pose proof (lval_firstn_S buf' (bn_top b1 - 1) ltac:(lia)) as HlS. replace (S (bn_top b1 - 1)) with (bn_top b1) in HlS by lia.
    rewrite E3, Z.mul_0_r, Z.add_0_r in HlS. fold q in HlS. split; [symmetry; exact HlS|].
    destruct (Nat.eq_dec (bn_top b1 - 1) 0) as [E0|E0]; [left; exact E0|right]. intros Ez.
    pose proof (lval_firstn_S buf' (bn_top b1 - 1 - 1) ltac:(lia)) as HlS2. replace (S (bn_top b1 - 1 - 1)) with (bn_top b1 - 1)%nat in HlS2 by lia.
    rewrite Ez, Z.mul_0_r, Z.add_0_r in HlS2.
    pose proof (lval_bound (firstn (bn_top b1 - 1 - 1) buf') (limbs_firstn _ _ Q1)) as HB3. rewrite firstn_length_le in HB3 by lia.
    pose proof (Bp_S (bn_top b1 - 1 - 1)) as HBS. replace (S (bn_top b1 - 1 - 1)) with (bn_top b1 - 1)%nat in HBS by lia.
    specialize (HB2 ltac:(lia)).
    assert (Hge : Bp (bn_top b1 - 1 - 1) <= q).
    { rewrite Hq. replace (Bp (bn_top b1 - 1 - 1)) with (Bp (bn_top b1 - 1) / BW) by (rewrite HBS, Z.mul_comm; apply Z.div_mul; lia).
      eapply Z.le_trans; [apply Z.div_le_mono; [lia|exact HB2]|]. apply Z.div_le_compat_l; lia. }
    lia. }
  destruct Hmag' as [M1 M2].
  apply HQ.
  - unfold bnv, bnw, bn_mag, bn_norm; cbn -[top' q Z.div]. rewrite <- Hq. split; [|exact M2].
    split; [exact Q1|]. split; [rewrite Q2; unfold top'; destruct (_ && _); lia|]. split; [exact M1|]. split; [destruct (top' =? 0)%nat; [reflexivity|exact Hneg1]|]. split; [exact Hff1|].
    split; [intros E; apply Hdd1 in E; apply (f_equal (@length Z)) in E; cbn in E|intros E; apply (f_equal (@length Z)) in E; rewrite Q2 in E; cbn in E].
    + destruct buf'; [reflexivity|rewrite <- Q2 in E; cbn in E; exfalso; lia].
    + destruct Hdd1 as [_ Hx]. apply Hx. destruct (bn_buf b1); [reflexivity|cbn in E; lia].
  - unfold bdm in *; cbn -[Z.of_nat Z.max Z.add] in *. rewrite Q2. lia.
  - cbn -[top']. unfold top'; destruct (_ && _); lia.
  - unfold bnb in *; cbn -[Z.of_nat Z.mul app] in *. rewrite Q2. exact HP1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma digits_aux_len10 : forall fuel dig x acc m, 0 <= x < 10 ^ m -> 0 <= m ->
  (length (digits_aux fuel 10 dig x acc) <= Z.to_nat m + length acc)%nat.
Proof.
  induction fuel as [|f IH]; intros dig x acc m Hx Hm; cbn [digits_aux]; [lia|].
  destruct (Z.eqb_spec x 0) as [->|NE]; [lia|].
  assert (Hm1 : 1 <= m). { destruct (Z.eq_dec m 0) as [E|E]; [|lia]. rewrite E in Hx. cbn in Hx. lia. }
  specialize (IH dig (x / 10) (dig (x mod 10) :: acc) (m - 1)). cbn [length] in IH.
  assert (Hx' : 0 <= x / 10 < 10 ^ (m - 1)).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. replace (10 * 10 ^ (m - 1)) with (10 ^ m); [lia|].
    replace m with (m - 1 + 1) at 1 by lia. rewrite Z.pow_add_r by lia. lia. }
  specialize (IH Hx' ltac:(lia)). lia.
Qed.

Lemma zdigits_le : forall v m, 0 <= v < 10 ^ m -> 1 <= m -> zdigits v <= m.
Proof.
  intros v m Hv Hm. unfold zdigits, zdec, zlength. destruct (Z.eqb_spec v 0) as [->|NE]; [cbn; lia|].
  unfold dec_digits. pose proof (digits_aux_len10 20 (fun d => 48 + d) v [] m Hv ltac:(lia)) as H. cbn [length] in H. lia.
Qed.

Lemma digits_aux_length' fuel base dig x acc : (length acc <= length (digits_aux fuel base dig x acc) <= fuel + length acc)%nat.
Proof. revert x acc. induction fuel as [|f IH]; intros x acc; cbn; [lia|]. destruct (x =? 0); cbn; [lia|]. specialize (IH (x / base) (dig (x mod base) :: acc)). cbn in IH. lia. Qed.

Lemma digits_aux_S' f base dig x acc :
  digits_aux (S f) base dig x acc = if x =? 0 then acc else digits_aux f base dig (x / base) (dig (x mod base) :: acc).
Proof. reflexivity. Qed.

Lemma zdigits_bound' v : 1 <= zdigits v <= 20.
Proof.
  unfold zdigits, zdec, zlength. destruct (Z.eqb_spec v 0) as [->|NE]; [cbn; lia|].
  unfold dec_digits. change 20%nat with (S 19). rewrite digits_aux_S'. destruct (Z.eqb_spec v 0) as [E|_]; [lia|].
  pose proof (digits_aux_length' 19 10 (fun v0 => 48 + v0) (v / 10) [48 + v mod 10]) as H.
  remember (digits_aux 19 10 (fun v0 : Z => 48 + v0) (v / 10) [48 + v mod 10]) as l. clear Heql. cbn [length] in H. lia.
Qed.

Definition numf (b : Z) : Z := b * 3 / 10 + b * 3 / 1000 + 1 + 1.

Lemma numf_mono : forall a b, a <= b -> numf a <= numf b.
Proof. intros a b H. unfold numf. pose proof (Z.div_le_mono (a * 3) (b * 3) 10 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (a * 3) (b * 3) 1000 ltac:(lia) ltac:(lia)). lia. Qed.

Lemma numf_ge2 : forall b, 0 <= b -> 2 <= numf b.
Proof. intros b H. unfold numf. pose proof (Z.div_pos (b * 3) 10 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos (b * 3) 1000 ltac:(lia) ltac:(lia)). lia. Qed.

Fixpoint chk210 (n : nat) (b p q : Z) {struct n} : bool :=
  match n with
  | O => true
  | S n' => (p <=? q) && chk210 n' (b + 1) (2 * p) (10 ^ (numf (b + 1) - numf b) * q)
  end.

Lemma chk210_spec : forall n b p q, chk210 n b p q = true -> 0 <= b -> p = 2 ^ b -> q = 10 ^ (numf b) ->
  forall b', b <= b' < b + Z.of_nat n -> 2 ^ b' <= 10 ^ (numf b').
Proof.
  induction n as [|n IH]; intros b p q H Hb Hp Hq b' Hb'; [lia|].
  cbn [chk210] in H. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1.
  destruct (Z.eq_dec b' b) as [->|NE]; [rewrite <- Hp, <- Hq; exact H1|].
  apply (IH (b + 1) (2 * p) (10 ^ (numf (b + 1) - numf b) * q) H2 ltac:(lia)); [| |lia].
  - rewrite Hp. rewrite Z.pow_add_r by lia. lia.
  - rewrite Hq. rewrite <- Z.pow_add_r; [f_equal; lia|pose proof (numf_mono b (b + 1) ltac:(lia)); lia|pose proof (numf_ge2 b Hb); lia].
Qed.

Lemma pow2_le_pow10 : forall b, 0 <= b <= 4200 -> 2 ^ b <= 10 ^ (numf b).
Proof.
  intros b Hb. apply (chk210_spec 4201 0 1 100); [vm_compute; reflexivity|lia|reflexivity|reflexivity|lia].
Qed.

Fixpoint wloop (fuel : nat) (v : Z) (acc : list Z) {struct fuel} : option (list Z) :=
  match fuel with
  | O => if v =? 0 then Some acc else None
  | S f => if v =? 0 then Some acc else wloop f (v / BN_DEC_CONV) ((v mod BN_DEC_CONV) :: acc)
  end.

Lemma wloop_zero : forall fuel acc, wloop fuel 0 acc = Some acc.
Proof. intros [|f] acc; reflexivity. Qed.

Lemma wloop_spec : forall fuel v acc, 0 < v -> v < BN_DEC_CONV ^ (Z.of_nat fuel) ->
  exists w0 tl, wloop fuel v acc = Some (w0 :: tl ++ acc) /\ 0 < w0 < BN_DEC_CONV /\
                w0 * BN_DEC_CONV ^ (zlength tl) <= v < (w0 + 1) * BN_DEC_CONV ^ (zlength tl).
Proof.
  induction fuel as [|f IH]; intros v acc Hv Hlt.
  - cbn in Hlt. lia.
  - cbn [wloop]. destruct (Z.eqb_spec v 0) as [E|_]; [lia|].
    assert (HD : 0 < BN_DEC_CONV) by (unfold BN_DEC_CONV; lia).
    pose proof (Z.div_mod v BN_DEC_CONV ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound v BN_DEC_CONV HD) as Hmb.
    destruct (Z.eq_dec (v / BN_DEC_CONV) 0) as [Ez|Ez].
    + rewrite Ez, wloop_zero. exists (v mod BN_DEC_CONV), []. cbn [app zlength length Z.of_nat]. rewrite Z.pow_0_r. split; [reflexivity|]. lia.
    + assert (Hq : 0 < v / BN_DEC_CONV) by (pose proof (Z.div_pos v BN_DEC_CONV ltac:(lia) HD); lia).
      assert (Hq2 : v / BN_DEC_CONV < BN_DEC_CONV ^ Z.of_nat f).
      { apply Z.div_lt_upper_bound; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hlt by lia. lia. }
      destruct (IH (v / BN_DEC_CONV) (v mod BN_DEC_CONV :: acc) Hq Hq2) as (w0 & tl & E1 & E2 & E3).
      exists w0, (tl ++ [v mod BN_DEC_CONV]). rewrite E1. rewrite <- app_assoc. cbn [app]. split; [reflexivity|]. split; [exact E2|].
      unfold zlength in *. rewrite length_app, Nat2Z.inj_add. cbn [length Z.of_nat Pos.of_succ_nat]. rewrite Z.pow_add_r, Z.pow_1_r by lia.
      pose proof (Z.pow_pos_nonneg BN_DEC_CONV (Z.of_nat (length tl)) HD ltac:(lia)). nia.
Qed.

Lemma bmalloc_bwp : forall n (bs : ST) L X0 X (Q : ptr * ST -> list (ptr * Z) -> Prop),
  roomy0 X0 -> Permutation X (L ++ X0) -> zlength L <= 7 -> bnonneg L -> 0 <= n -> bsum L + n <= 16000 ->
  (forall p X', Permutation X' ((p, n) :: L ++ X0) -> Q (p, bs) X') -> bwp (bmalloc ops n bs) X Q.
Proof.
  intros n bs L X0 X Q HR HP HLc HLn Hn Hsz HQ. unfold bmalloc. cbn. pose proof (bnonneg_sum L HLn).
  split; [apply lt62c; lia|]. split; [apply (ok_bn X L X0); try assumption; lia|]. split; [reflexivity|].
  intros p Hp. apply HQ. apply perm_skip. exact HP.
Qed.

Lemma bfree_bwp : forall p n (bs : ST) X' X (Q : unit * ST -> list (ptr * Z) -> Prop),
  Permutation X ((p, n) :: X') -> Q (tt, bs) X' -> bwp (bfree ops p bs) X Q.
Proof. intros p n bs X' X Q HP HQ. unfold bfree. cbn. exists n, X'. split; [exact HP|exact HQ]. Qed.

Lemma RT2 : (RT < 2)%nat. Proof. unfold RT. lia. Qed.
Lemma RBL2 : (RBL < 2)%nat. Proof. unfold RBL. lia. Qed.
Lemma RT_RBL : RT <> RBL. Proof. unfold RT, RBL. lia. Qed.

Lemma is_zero_pure_iff (b : BN) v : bnv b v -> is_zero_pure b = (v =? 0).
Proof.
  intros Hb. unfold is_zero_pure. pose proof (bnv_zero_iff b v Hb) as [A B].
  destruct (Nat.eqb_spec (bn_top b) 0) as [E|E]; destruct (Z.eqb_spec v 0) as [E'|E']; try reflexivity; exfalso; [apply E', A, E|apply E, B, E'].
Qed.

(* [comment removed for export] *)
Lemma bn2dec_loop_bwp : forall fuel (bs : ST) v acc (kt : nat) L X0 X (Q : option (list Z) * ST -> list (ptr * Z) -> Prop),
  st2 bs -> bnv (getbn RT bs) v -> v < Bp kt -> Z.of_nat kt <= 65 -> bdm (getbn RT bs) <= Z.of_nat kt + 1 -> roomy0 X0 ->
  Permutation X (bnb (getbn RT bs) ++ L ++ X0) -> zlength L <= 6 -> bnonneg L -> bsum L + 16 * (Z.of_nat kt + 1) <= 16000 ->
  (forall b' v' X', bnv b' v' -> 0 <= v' <= v -> bdm b' <= Z.of_nat kt + 1 -> Permutation X' (bnb b' ++ L ++ X0) ->
      (wloop fuel v acc <> None -> v' = 0) -> Q (wloop fuel v acc, setbn RT b' bs) X') ->
  bwp (bn2dec_loop ops fuel RT acc bs) X Q.
Proof.
  induction fuel as [|f IH]; intros bs v acc kt L X0 X Q H2 Hb Hv Hkt Hd HR HP HLc HLn Hsz HQ;
    pose proof (bnv_bounds _ _ Hb) as [HB1 HB2]; cbn [bn2dec_loop]; cbn [wloop] in HQ.
  - apply bwp_bbind. cbn [bget ret tree_ops ApLogic.bwp fst snd]. rewrite (is_zero_pure_iff _ _ Hb).
    pose proof (HQ (getbn RT bs) v X Hb ltac:(lia) Hd HP) as HQ'. rewrite setbn_getbn_id in HQ'.
    destruct (Z.eqb_spec v 0) as [E|E]; cbn; apply HQ'; [lia|intros C; exfalso; apply C; reflexivity].
  - apply bwp_bbind. cbn [bget ret tree_ops ApLogic.bwp fst snd]. rewrite (is_zero_pure_iff _ _ Hb).
    destruct (Z.eqb_spec v 0) as [E|E]; cbn -[BN_div_word bn2dec_loop wloop bbind getbn setbn BN_DEC_CONV Z.div Z.modulo].
    { pose proof (HQ (getbn RT bs) v X Hb ltac:(lia) Hd HP) as HQ'. rewrite setbn_getbn_id in HQ'. apply HQ'. lia. }
    pose proof (bnv_top_le _ _ _ Hb Hv) as Htk.
    apply bwp_bbind. eapply BN_div_word_bwp; [exact H2|exact RT2|exact Hb|lia|exact HR|exact HP|exact HLc|exact HLn|unfold bdm in *; lia|].
    intros b1 X1 Hb1 Hd1 Ht1 HP1. cbn [fst snd].
    assert (HD : 0 < BN_DEC_CONV) by (unfold BN_DEC_CONV; lia).
    assert (Hq : 0 <= v / BN_DEC_CONV <= v). { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. unfold BN_DEC_CONV; nia. }
    eapply (IH (setbn RT b1 bs) (v / BN_DEC_CONV) _ kt L X0 X1);
      [apply st2_setbn; exact H2|rewrite (getbn_setbn_same2 RT b1 bs H2 RT2); exact Hb1|lia|exact Hkt|rewrite (getbn_setbn_same2 RT b1 bs H2 RT2); lia|exact HR
      |rewrite (getbn_setbn_same2 RT b1 bs H2 RT2); exact HP1|exact HLc|exact HLn|exact Hsz|].
    intros b' v' X' Hb' Hv' Hd' HP' Hz. rewrite setbn_setbn_same. apply (HQ b' v' X'); [exact Hb'|lia|exact Hd'|exact HP'|exact Hz].
Qed.

Lemma zl_cons {A} (x : A) l : zlength (x :: l) = zlength l + 1.
Proof. unfold zlength. cbn [length]. lia. Qed.

Lemma numf_4102 : numf 4102 = 1244. Proof. reflexivity. Qed.

Lemma pow2_4102_Bp65 : 2 ^ 4102 <= Bp 65.
Proof. rewrite Bp_is_pow. apply Z.pow_le_mono_r; lia. Qed.

Lemma BN_bn2dec_bwp : forall (bs : ST) v bb L X0 X (Q : (ptr * Z) * ST -> list (ptr * Z) -> Prop),
  st2 bs -> bnv (getbn RBL bs) v -> 0 <= bb <= 4102 -> v < 2 ^ bb -> roomy0 X0 ->
  Permutation X (bnb (getbn RBL bs) ++ L ++ X0) -> zlength L <= 1 -> bnonneg L -> bsum L <= 24 -> bdm (getbn RBL bs) <= 66 ->
  (forall buf tb slen bs' X', st2 bs' -> getbn RBL bs' = getbn RBL bs -> 0 <= tb <= numf bb + 3 -> 1 <= slen <= numf bb ->
      Permutation X' ((buf, tb) :: bnb (getbn RBL bs) ++ L ++ X0) -> Q ((buf, slen), bs') X') ->
  bwp (BN_bn2dec ops RT RBL bs) X Q.
Proof.
  intros bs v bb L X0 X Q H2 Hb Hbb Hvb HR HP HLc HLn Hsz Hdm HQ. pose proof Hb as ((Hl & Ht & Hm & Hneg & Hf & Hd) & Hnorm).
  pose proof (bnv_bounds _ _ Hb) as [HB1 HB2]. destruct (bnb_facts _ _ (bnv_w _ _ Hb)) as (F1 & F2 & F3 & F4). pose proof (bnonneg_sum L HLn) as HL0.
  assert (Htop : (bn_top (getbn RBL bs) <= 65)%nat). { apply (bnv_top_le _ v); [exact Hb|]. pose proof pow2_4102_Bp65. pose proof (Z.pow_le_mono_r 2 bb 4102 ltac:(lia) ltac:(lia)). lia. }
  unfold BN_bn2dec. apply bwp_bbind. cbn [bget ret tree_ops ApLogic.bwp fst snd].
  set (a := getbn RBL bs) in *.
  pose proof (num_bits_pure_spec a (bnv_okv _ _ (bnv_w _ _ Hb)) Hnorm) as (N1 & N2 & N3 & N4). rewrite Hm in N2, N3.
  set (nb := num_bits_pure a) in *.
  assert (Hnb : nb <= bb).
  { destruct (Z.eq_dec v 0) as [E|E]; [rewrite (N2 E); lia|]. specialize (N3 ltac:(lia)).
    destruct (Z.le_gt_cases nb bb) as [C|C]; [exact C|]. exfalso. pose proof (Z.pow_le_mono_r 2 bb (nb - 1) ltac:(lia) ltac:(lia)). lia. }
  change (nb * 3 / 10 + nb * 3 / 1000 + 1 + 1) with (numf nb).
  pose proof (numf_mono nb bb Hnb) as M1. pose proof (numf_mono bb 4102 ltac:(lia)) as M2. rewrite numf_4102 in M2. pose proof (numf_ge2 nb N1) as M3.
  set (num := numf nb) in *.
  unfold BN_DEC_NUM.
  pose proof (Z.div_pos num 19 ltac:(lia) ltac:(lia)) as Dv1. pose proof (Z.div_le_mono num 1244 19 ltac:(lia) ltac:(lia)) as Dv2. change (1244 / 19) with 65 in Dv2.
  (* [comment removed for export] *)
  apply bwp_bbind. eapply (bmalloc_bwp _ bs (bnb a ++ L) X0 X); [exact HR|rewrite <- app_assoc; exact HP|rewrite zlen_app'; lia|apply bnonneg_app; assumption|lia|rewrite bsum_app; lia|].
  intros bn_data X1 HP1. cbn [fst snd].
  set (L1 := (bn_data, (num / 19 + 1) * 8) :: bnb a ++ L) in *.
  assert (HL1 : zlength L1 <= 3 /\ bnonneg L1 /\ bsum L1 <= 528 + 528 + 24).
  { unfold L1. rewrite zl_cons, zlen_app', bsum_cons, bsum_app. cbn [snd]. split; [lia|]. split; [apply Forall_cons; [cbn; lia|apply bnonneg_app; assumption]|]. lia. }
  destruct HL1 as (HL1a & HL1b & HL1c).
  apply bwp_bbind. eapply (bmalloc_bwp _ bs L1 X0 X1); [exact HR|exact HP1|lia|exact HL1b|lia|lia|].
  intros buf X2 HP2. cbn [fst snd].
  set (L2 := (buf, num + 3) :: L1) in *.
  assert (HL2 : zlength L2 <= 4 /\ bnonneg L2 /\ bsum L2 <= 1247 + 528 + 528 + 24).
  { unfold L2. rewrite zl_cons, bsum_cons. cbn [snd]. split; [lia|]. split; [apply Forall_cons; [cbn; lia|exact HL1b]|]. lia. }
  destruct HL2 as (HL2a & HL2b & HL2c).
  (* [comment removed for export] *)
  apply bwp_bbind. eapply (BN_dup_bwp RT RBL bs v L2 X0 X2); [exact H2|exact RT2|exact RBL2|exact RT_RBL|exact Hb|fold a; lia|exact HR|exact HP2|lia|exact HL2b|fold a; lia|].
  intros tp t X3 Htv Htd Htt HP3. cbn [fst snd]. fold a in Htd, Htt.
  apply bwp_bbind. cbn [bget ret tree_ops ApLogic.bwp fst snd]. rewrite (getbn_setbn_same2 RT t bs H2 RT2). rewrite (is_zero_pure_iff _ _ Htv).
  pose proof Htv as ((Tl & Tt & Tm & Tneg & Tf & Td) & Tnorm).
  set (L3 := (tp, 24) :: L2) in *.
  assert (HL3 : zlength L3 <= 5 /\ bnonneg L3 /\ bsum L3 <= 24 + 1247 + 528 + 528 + 24).
  { unfold L3. rewrite zl_cons, bsum_cons. cbn [snd]. split; [lia|]. split; [apply Forall_cons; [cbn; lia|exact HL2b]|]. lia. }
  destruct HL3 as (HL3a & HL3b & HL3c).
  (* [comment removed for export] *)
  assert (TAIL : forall slen t' v' X', bnv t' v' -> 1 <= slen <= num -> Permutation X' (bnb t' ++ L3 ++ X0) ->
     bwp (bbind ops (bfree ops bn_data) (fun _ => bbind ops (BN_free ops RT (Some tp)) (fun _ => bret ops (buf, slen))) (setbn RT t' bs)) X' Q).
  { intros slen t' v' X' Ht' Hsl HP'.
    apply bwp_bbind. eapply (bfree_bwp bn_data ((num / 19 + 1) * 8) _ (bnb t' ++ ((tp, 24) :: (buf, num + 3) :: bnb a ++ L) ++ X0)).
    { eapply Permutation_trans; [exact HP'|]. unfold L3, L2, L1. perm_solve. }
    cbn [fst snd]. apply bwp_bbind. eapply (BN_free_bwp RT _ tp v' ((buf, num + 3) :: bnb a ++ L) X0).
    { apply st2_setbn; exact H2. } { exact RT2. } { rewrite (getbn_setbn_same2 RT t' bs H2 RT2). exact Ht'. }
    { rewrite (getbn_setbn_same2 RT t' bs H2 RT2). perm_solve. }
    intros X'' HP''. cbn [fst snd bret ret tree_ops ApLogic.bwp]. rewrite setbn_setbn_same. apply (HQ buf (num + 3) slen _ X'').
    - apply st2_setbn; exact H2.
    - apply getbn_setbn_other2. exact RT_RBL.
    - lia.
    - lia.
    - eapply Permutation_trans; [exact HP''|]. perm_solve. }
  destruct (Z.eqb_spec v 0) as [Ez|Ez].
  { (* [comment removed for export] *) cbn -[bfree BN_free bret bbind setbn getbn Z.add Z.mul Z.div]. apply bwp_bbind. cbn [bret ret tree_ops ApLogic.bwp fst snd].
    apply (TAIL 1 t v X3); [exact Htv|lia|exact HP3]. }
  cbn -[bfree BN_free bret bbind setbn getbn Z.add Z.mul Z.div bn2dec_loop Z.to_nat zdigits zlength Z.leb].
  apply bwp_bbind. apply bwp_bbind.
  eapply (bn2dec_loop_bwp (Z.to_nat (num / 19 + 1)) (setbn RT t bs) v [] (bn_top a) L3 X0 X3);
    [apply st2_setbn; exact H2|rewrite (getbn_setbn_same2 RT t bs H2 RT2); exact Htv|lia|lia|rewrite (getbn_setbn_same2 RT t bs H2 RT2); lia|exact HR
    |rewrite (getbn_setbn_same2 RT t bs H2 RT2); exact HP3|lia|exact HL3b|lia|].
  intros t' v' X4 Ht' Hv' Hd' HP4 Hz. rewrite setbn_setbn_same. cbn [fst snd].
  (* [comment removed for export] *)
  assert (HD : 0 < BN_DEC_CONV) by (unfold BN_DEC_CONV; lia).
  assert (Hv10 : v < 10 ^ num).
  { specialize (N3 ltac:(lia)). pose proof (pow2_le_pow10 nb ltac:(lia)). unfold num. lia. }
  assert (HF : Z.of_nat (Z.to_nat (num / 19 + 1)) = num / 19 + 1) by (apply Z2Nat.id; lia).
  assert (HvF : v < BN_DEC_CONV ^ Z.of_nat (Z.to_nat (num / 19 + 1))).
  { rewrite HF. unfold BN_DEC_CONV. change 10000000000000000000 with (10 ^ 19). rewrite <- Z.pow_mul_r by lia.
    eapply Z.lt_le_trans; [exact Hv10|]. apply Z.pow_le_mono_r; [lia|]. pose proof (Z.div_mod num 19 ltac:(lia)). pose proof (Z.mod_pos_bound num 19 ltac:(lia)). lia. }
  destruct (wloop_spec (Z.to_nat (num / 19 + 1)) v [] ltac:(lia) HvF) as (w0 & tl & W1 & W2 & W3). rewrite app_nil_r in W1.
  rewrite W1. rewrite W1 in Hz. cbn -[bfree BN_free bret bbind setbn getbn Z.add Z.mul Z.div zdigits zlength Z.leb].
  rewrite ?Tneg, ?Hneg.
  set (slen := 0 + zdigits w0 + 19 * zlength tl).
  assert (Hslen : 1 <= slen <= num).
  { pose proof (zdigits_bound' w0) as ZB. assert (Hlen0 : 0 <= zlength tl) by (unfold zlength; lia).
    assert (E19 : BN_DEC_CONV ^ zlength tl = 10 ^ (19 * zlength tl)).
    { unfold BN_DEC_CONV. change 10000000000000000000 with (10 ^ 19). rewrite <- Z.pow_mul_r by lia. reflexivity. }
    rewrite E19 in W3. pose proof (Z.pow_pos_nonneg 10 (19 * zlength tl) ltac:(lia) ltac:(lia)) as P19.
    assert (Hlt : 19 * zlength tl < num).
    { destruct (Z.lt_ge_cases (19 * zlength tl) num) as [C|C]; [exact C|]. exfalso.
      pose proof (Z.pow_le_mono_r 10 num (19 * zlength tl) ltac:(lia) C). nia. }
    assert (Hw0 : w0 < 10 ^ (num - 19 * zlength tl)).
    { destruct (Z.lt_ge_cases w0 (10 ^ (num - 19 * zlength tl))) as [C|C]; [exact C|]. exfalso.
      assert (E : 10 ^ num = 10 ^ (num - 19 * zlength tl) * 10 ^ (19 * zlength tl)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      pose proof (Z.pow_pos_nonneg 10 (num - 19 * zlength tl) ltac:(lia) ltac:(lia)). nia. }
    pose proof (zdigits_le w0 (num - 19 * zlength tl) ltac:(lia) ltac:(lia)). unfold slen. lia. }
  destruct (Z.leb_spec (num + 3) slen) as [C|C]; [exfalso; lia|].
  cbn [bret ret tree_ops ApLogic.bwp fst snd].
  apply (TAIL slen t' v' X4); [exact Ht'|exact Hslen|exact HP4].
Qed.
End BnSpec2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lor_lt_pow2 : forall a b n, 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
  intros a b n Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec a 0) as [->|NA]; [rewrite Z.lor_0_l; lia|]. destruct (Z.eq_dec b 0) as [->|NB]; [rewrite Z.lor_comm, Z.lor_0_l; lia|].
  assert (Hn : 0 <= n). { destruct (Z.lt_ge_cases n 0) as [C|C]; [|exact C]. rewrite Z.pow_neg_r in Ha by exact C. lia. }
  assert (Hp : 0 < Z.lor a b). { pose proof (proj2 (Z.lor_nonneg a b) ltac:(lia)). destruct (Z.eq_dec (Z.lor a b) 0) as [E|E]; [|lia]. apply Z.lor_eq_0_iff in E. lia. }
  apply Z.log2_lt_pow2; [exact Hp|]. rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

Lemma land127 : forall c, 0 <= Z.land c 127 < 128.
Proof. intros c. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Lemma land_mask64 : forall x, 0 <= x -> 0 <= Z.land x (BW - 1) <= x /\ Z.land x (BW - 1) < 2 ^ 64.
Proof.
  intros x Hx. rewrite BW_pow. change (2 ^ 64 - 1) with (Z.ones 64). rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)). pose proof (Z.mod_le x (2 ^ 64) Hx ltac:(lia)). lia.
Qed.

Lemma pow128_le_pow1000 : forall k, 0 <= k -> 2 ^ (7 * k) <= 10 ^ (3 * k).
Proof. intros k Hk. rewrite !Z.pow_mul_r by lia. apply Z.pow_le_mono_l. split; [lia|]. cbn. lia. Qed.

Lemma numf_7k : forall k, 3 <= k -> numf (7 * k) <= 3 * k.
Proof.
  intros k Hk. unfold numf.
  pose proof (Z.mul_div_le (7 * k * 3) 10 ltac:(lia)). pose proof (Z.mul_div_le (7 * k * 3) 1000 ltac:(lia)). lia.
Qed.

Lemma ULONG_MAX_SHR7_eq : ULONG_MAX_SHR7 = 2 ^ 57 - 1.
Proof. reflexivity. Qed.

Section O2T.
Context {ptr : Type}.
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ST := (bstate ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).
Local Notation okA := (okAp (ptr:=ptr) AP_NB AP_TOT) (only parsing).
Local Notation bwp := (bwp (okAp (ptr:=ptr) AP_NB AP_TOT)) (only parsing).

(* [comment removed for export] *)
Definition OI (X0 : list (ptr * Z)) (kb : Z) (st : o2t) (blp : option ptr) (bs : ST) (X : list (ptr * Z)) : Prop :=
  st2 bs /\ 0 <= o_n st /\ 0 <= kb /\
  (o_insub st = false -> o_bn st = false /\ kb = 0) /\
  (o_insub st = true -> o_bn st = false -> 0 <= o_l st < 2 ^ 64 /\ o_l st < 2 ^ (7 * (kb + 1))) /\
  match blp with
  | None => o_bn st = false /\ Permutation X X0
  | Some p => exists vb, bnv (getbn RBL bs) vb /\ bdm (getbn RBL bs) <= 66 /\ Permutation X ((p, 24) :: bnb (getbn RBL bs) ++ X0) /\
      (o_bn st = true -> ULONG_MAX_SHR7 < o_l st /\ 2 ^ 57 <= vb /\ vb < 2 ^ (7 * (kb + 1)))
  end.

(* [comment removed for export] *)
Definition OIend (X0 : list (ptr * Z)) (blp : option ptr) (bs : ST) (X : list (ptr * Z)) : Prop :=
  st2 bs /\
  match blp with
  | None => Permutation X X0
  | Some p => exists vb, bnv (getbn RBL bs) vb /\ Permutation X ((p, 24) :: bnb (getbn RBL bs) ++ X0)
  end.

Lemma pow7_mono a b : 0 <= a <= b -> 2 ^ (7 * a) <= 2 ^ (7 * b).
Proof. intros H. apply Z.pow_le_mono_r; lia. Qed.

Lemma top65 (b : BN) v k : bnv b v -> 0 <= v -> v < 2 ^ (7 * k) -> 0 <= k <= 586 -> (bn_top b <= 65)%nat.
Proof.
  intros Hb Hv Hk Hkk. apply (bnv_top_le b v 65 Hb). pose proof pow2_4102_Bp65. pose proof (Z.pow_le_mono_r 2 (7 * k) 4102 ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma o2t_emit_bwp : forall st blp (bs : ST) X X0 kb,
  roomy0 X0 -> OI X0 kb st blp bs X -> o_insub st = true -> kb + 1 <= 586 ->
  (o_bn st = true -> exists p vb, blp = Some p /\ bnv (getbn RBL bs) vb /\ 2 ^ 57 <= vb /\ vb < 2 ^ (7 * (kb + 1))) ->
  bwp (o2t_emit ops st blp bs) X (fun r X' => let '(st', blp', bs') := (fst (fst r), snd (fst r), snd r) in
        OI X0 0 st' blp' bs' X' /\ o_insub st' = false /\ o_bn st' = false /\ blp' = blp /\ o_n st' <= o_n st + 2 + 3 * (kb + 1)).
Proof.
  intros st blp bs X X0 kb HR HI Hins Hkb Hbn.
  assert (EBW : BW = 18446744073709551616) by (rewrite BW_pow; reflexivity).
  assert (E57 : 2 ^ 57 = 144115188075855872) by reflexivity.
  destruct HI as (H2 & Hn0 & Hkb0 & Hout & Hin & Hblp).
  unfold o2t_emit.
  destruct (o_bn st) eqn:Ebn.
  - (* [comment removed for export] *)
    destruct (Hbn eq_refl) as (p & vb & Eblp & Hb & Hvlo & Hvhi). subst blp.
    destruct Hblp as (vb' & Hb' & Hdm & HP & _).
    assert (Evb : vb' = vb). { destruct Hb as ((_ & _ & M & _) & _). destruct Hb' as ((_ & _ & M' & _) & _). congruence. } subst vb'.
    assert (Hk9 : 9 <= kb + 1).
    { destruct (Z.lt_ge_cases (kb + 1) 9) as [C|C]; [|exact C]. exfalso. pose proof (Z.pow_le_mono_r 2 (7 * (kb + 1)) 56 ltac:(lia) ltac:(lia)).
      assert (2 ^ 56 < 2 ^ 57) by (apply Z.pow_lt_mono_r; lia). lia. }
    (* [comment removed for export] *)
    apply bwp_bbind.
    assert (STEP1 : bwp ((if o_first st then bbind ops (bget ops RBL) (fun _ => bbind ops (BN_sub_word ops RBL 80) (fun _ => bret ops (mkO2T (o_l st) true (o_insub st) false (o_n st + 1)))) else bret ops st) bs) X
              (fun r X' => X' = X /\ o_bn (fst r) = true /\ o_n st <= o_n (fst r) <= o_n st + 1 /\ 0 <= o_n (fst r) /\
                 exists b' v', snd r = setbn RBL b' bs /\ bnv b' v' /\ 0 <= v' < 2 ^ (7 * (kb + 1)) /\ bdm b' <= 66 /\ bnb b' = bnb (getbn RBL bs))).
    { destruct (o_first st).
      - apply bwp_bbind. cbn [bget ret tree_ops ApLogic.bwp fst snd]. apply bwp_bbind.
        eapply BN_sub_word_bwp; [exact H2|exact RBL2|exact Hb|lia|lia|].
        intros b' Hb2 Hd2 Ht2 Hbb2. cbn. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
        exists b', (vb - 80). split; [reflexivity|]. split; [exact Hb2|]. split; [lia|]. split; [lia|]. exact Hbb2.
      - cbn. split; [reflexivity|]. split; [exact Ebn|]. split; [lia|]. split; [lia|]. exists (getbn RBL bs), vb. rewrite setbn_getbn_id.
        split; [reflexivity|]. split; [exact Hb|]. split; [lia|]. split; [exact Hdm|reflexivity]. }
    eapply bwp_mono; [exact STEP1|]. intros [st1 bs1] X1 (-> & Ebn1 & Hn1 & Hn1' & b' & v' & -> & Hb2 & Hv2 & Hd2 & Hbb2). cbn [fst snd] in *.
    rewrite Ebn1. apply bwp_bbind.
    eapply (BN_bn2dec_bwp (setbn RBL b' bs) v' (7 * (kb + 1)) [(p, 24)] X0 X);
      [apply st2_setbn; exact H2|rewrite (getbn_setbn_same2 RBL b' bs H2 RBL2); exact Hb2|lia|lia|exact HR
      |rewrite (getbn_setbn_same2 RBL b' bs H2 RBL2), Hbb2; eapply Permutation_trans; [exact HP|]; perm_solve
      |unfold zlength; cbn; lia|apply Forall_cons; [cbn; lia|apply Forall_nil]|unfold bsum; cbn; lia|rewrite (getbn_setbn_same2 RBL b' bs H2 RBL2); exact Hd2|].
    intros buf tb slen bs' X' H2' Hget Htb Hsl HP'. cbn [fst snd]. rewrite (getbn_setbn_same2 RBL b' bs H2 RBL2) in Hget, HP'.
    apply bwp_bbind. eapply (bfree_bwp buf tb bs' ((p, 24) :: bnb b' ++ X0)); [eapply Permutation_trans; [exact HP'|]; perm_solve|].
    cbn. pose proof (numf_7k (kb + 1) ltac:(lia)) as N7.
    split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|lia]]]].
    unfold OI; cbn. split; [exact H2'|]. split; [lia|]. split; [lia|]. split; [intros _; split; [reflexivity|reflexivity]|]. split; [intros E; discriminate E|].
    exists v'. rewrite Hget. split; [exact Hb2|]. split; [exact Hd2|]. split; [rewrite Hbb2; exact (Permutation_refl _) || (rewrite Hbb2; apply Permutation_refl)|]. intros E; discriminate E.
  - (* [comment removed for export] *)
    destruct (Hin Hins eq_refl) as [Hl1 Hl2].
    pose proof (pow128_le_pow1000 (kb + 1) ltac:(lia)) as P3.
    assert (STEP1 : bwp ((if o_first st then (if 80 <=? o_l st then bret ops (mkO2T (o_l st - 80) false (o_insub st) false (o_n st + 1))
                                             else bret ops (mkO2T (o_l st - o_l st / 40 * 40) false (o_insub st) false (o_n st + 1)))
                          else bret ops st) bs) X
              (fun r X' => X' = X /\ snd r = bs /\ o_bn (fst r) = false /\ o_n st <= o_n (fst r) <= o_n st + 1 /\ 0 <= o_l (fst r) <= o_l st)).
    { pose proof (Z.mul_div_le (o_l st) 40 ltac:(lia)). pose proof (Z.div_pos (o_l st) 40 ltac:(lia) ltac:(lia)).
      destruct (o_first st); [destruct (Z.leb_spec 80 (o_l st))|]; cbn; repeat split; try reflexivity; try lia; try exact Ebn; nia. }
    apply bwp_bbind. eapply bwp_mono; [exact STEP1|]. intros [st1 bs1] X1 (-> & -> & Ebn1 & Hn1 & Hl3). cbn [fst snd] in *.
    rewrite Ebn1. cbn -[Z.add dotlu_len Z.mul].
    pose proof (zdigits_le (o_l st1) (3 * (kb + 1)) ltac:(lia) ltac:(lia)) as ZD. pose proof (zdigits_bound' (o_l st1)) as ZB. unfold dotlu_len.
    split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|lia]]]].
    unfold OI; cbn. split; [exact H2|]. split; [lia|]. split; [lia|]. split; [intros _; split; reflexivity|]. split; [intros E; discriminate E|].
    destruct blp as [p|].
    + destruct Hblp as (vb & Hb & Hdm & HP & _). exists vb. split; [exact Hb|]. split; [exact Hdm|]. split; [exact HP|]. intros E; discriminate E.
    + destruct Hblp as [_ HP]. split; [reflexivity|exact HP].
Qed.

(* [comment removed for export] *)
Definition o2t_body (c : Z) (rest : list Z) (st : o2t) (blp : option ptr) : BM (M:=btree ptr) (ptr:=ptr) (option Z * option ptr) :=
  let st := if o_insub st then st else mkO2T 0 false true (o_first st) (o_n st) in
  let low := Z.land c 127 in
  let cont := negb (Z.land c 128 =? 0) in
  bbind ops (if o_bn st then bbind ops (BN_add_word ops RBL low) (fun _ => bret ops st)
             else bret ops (mkO2T (Z.lor (o_l st) low) false true (o_first st) (o_n st)))
  (fun st1 =>
    if negb cont then
      bbind ops (o2t_emit ops st1 blp) (fun x => let '(st2, blp2) := x in o2t_bytes ops rest st2 blp2)
    else
      bbind ops (if negb (o_bn st1) && (ULONG_MAX_SHR7 <? o_l st1) then
                   bbind ops (match blp with
                              | None => bbind ops (BN_new ops RBL) (fun p => bret ops (Some p))
                              | Some p => bret ops (Some p)
                              end)
                   (fun blp' => bbind ops (BN_set_word ops RBL (o_l st1)) (fun _ => bret ops (mkO2T (o_l st1) true true (o_first st1) (o_n st1), blp')))
                 else bret ops (st1, blp))
      (fun x => let '(st2, blp2) := x in
         if o_bn st2 then bbind ops (BN_lshift ops RBL RBL 7) (fun _ => o2t_bytes ops rest st2 blp2)
         else o2t_bytes ops rest (mkO2T (Z.land (Z.shiftl (o_l st2) 7) (BW - 1)) false true (o_first st2) (o_n st2)) blp2)).

Lemma o2t_bytes_cons : forall c rest st blp,
  o2t_bytes ops (c :: rest) st blp =
  if (match rest with [] => negb (Z.land c 128 =? 0) | _ => false end) then bret ops (None, blp) else o2t_body c rest st blp.
Proof.
  intros c rest st blp. unfold o2t_body. cbn [o2t_bytes]. destruct rest as [|c' rest']; destruct (negb (Z.land c 128 =? 0)); reflexivity.
Qed.

Lemma div128_bound : forall vb kb, 0 <= kb -> (128 | vb) -> vb < 2 ^ (7 * (kb + 1)) -> vb + 128 <= 2 ^ (7 * (kb + 1)).
Proof.
  intros vb kb Hkb [m ->] Hlt. replace (7 * (kb + 1)) with (7 * kb + 7) in * by lia. rewrite Z.pow_add_r in * by lia.
  change (2 ^ 7) with 128 in *. pose proof (Z.pow_pos_nonneg 2 (7 * kb) ltac:(lia) ltac:(lia)). nia.
Qed.

Lemma o2t_bytes_bwp : forall bytes st blp (bs : ST) X X0 kb tot,
  roomy0 X0 -> OI X0 kb st blp bs X -> 0 <= tot -> tot + zlength bytes <= 586 -> kb <= tot -> o_n st <= 5 * (tot - kb) ->
  (o_bn st = true -> (128 | bn_mag (getbn RBL bs))) ->
  bwp (o2t_bytes ops bytes st blp bs) X (fun r X' =>
      OIend X0 (snd (fst r)) (snd r) X' /\ match fst (fst r) with Some n => 0 <= n <= 5 * (tot + zlength bytes) | None => True end).
Proof.
  induction bytes as [|c rest IH]; intros st blp bs X X0 kb tot HR HI Htot Hlen Hkt Hn Hdiv.
  { cbn. destruct HI as (H2 & Hn0 & Hkb0 & Hout & Hin & Hblp). split; [|unfold zlength; cbn; lia]. split; [exact H2|].
    destruct blp as [p|]; [destruct Hblp as (vb & Hb & Hdm & HP & _); exists vb; split; [exact Hb|exact HP]|exact (proj2 Hblp)]. }
  assert (EBW : BW = 18446744073709551616) by (rewrite BW_pow; reflexivity).
  assert (E57 : 2 ^ 57 = 144115188075855872) by reflexivity.
  rewrite zl_cons in Hlen. assert (Hzl : 0 <= zlength rest) by (unfold zlength; lia).
  rewrite o2t_bytes_cons.
  destruct (match rest with [] => negb (Z.land c 128 =? 0) | _ => false end).
  { cbn. destruct HI as (H2 & Hn0 & Hkb0 & Hout & Hin & Hblp). split; [|exact I]. split; [exact H2|].
    destruct blp as [p|]; [destruct Hblp as (vb & Hb & Hdm & HP & _); exists vb; split; [exact Hb|exact HP]|exact (proj2 Hblp)]. }
  unfold o2t_body.
  set (st0 := if o_insub st then st else mkO2T 0 false true (o_first st) (o_n st)).
  assert (HI0 : OI X0 kb st0 blp bs X /\ o_insub st0 = true /\ o_n st0 = o_n st /\ o_bn st0 = o_bn st).
  { unfold st0. destruct HI as (H2 & Hn0 & Hkb0 & Hout & Hin & Hblp). destruct (o_insub st) eqn:Eins.
    - split; [|split; [exact Eins|split; [reflexivity|reflexivity]]]. split; [exact H2|]. split; [exact Hn0|]. split; [exact Hkb0|]. split; [rewrite Eins; exact Hout|]. split; [rewrite Eins; exact Hin|exact Hblp].
    - destruct (Hout eq_refl) as [Ebn Ekb]. split; [|split; [reflexivity|split; [reflexivity|cbn; symmetry; exact Ebn]]].
      unfold OI; cbn. split; [exact H2|]. split; [exact Hn0|]. split; [lia|]. split; [intros E; discriminate E|]. split.
      { intros _ _. subst kb. change (2 ^ (7 * (0 + 1))) with 128. lia. }
      destruct blp as [p|]; [|split; [reflexivity|exact (proj2 Hblp)]].
      destruct Hblp as (vb & Hb & Hdm & HP & _). exists vb. split; [exact Hb|]. split; [exact Hdm|]. split; [exact HP|]. intros E; discriminate E. }
  clearbody st0. destruct HI0 as (HI0 & Hins0 & Hn0' & Hbn0). clear HI.
  rewrite <- Hbn0 in Hdiv.
  pose proof (land127 c) as Hlow. set (low := Z.land c 127) in *.
  destruct HI0 as (H2 & Hn0 & Hkb0 & Hout & Hin & Hblp).
  (* [comment removed for export] *)
  apply bwp_bbind.
  assert (ACC : bwp ((if o_bn st0 then bbind ops (BN_add_word ops RBL low) (fun _ => bret ops st0)
                      else bret ops (mkO2T (Z.lor (o_l st0) low) false true (o_first st0) (o_n st0))) bs) X
     (fun r X' => o_insub (fst r) = true /\ o_n (fst r) = o_n st /\ o_bn (fst r) = o_bn st0 /\ OI X0 kb (fst r) blp (snd r) X' /\
        (o_bn (fst r) = true -> exists p vb, blp = Some p /\ bnv (getbn RBL (snd r)) vb /\ 2 ^ 57 <= vb /\ vb < 2 ^ (7 * (kb + 1))) /\
        (o_bn (fst r) = false -> snd r = bs /\ X' = X))).
  { destruct (o_bn st0) eqn:Ebn.
    - destruct blp as [p|]; [|destruct Hblp as [E _]; discriminate E].
      destruct Hblp as (vb & Hb & Hdm & HP & Hx). destruct (Hx eq_refl) as (Hshr & Hvlo & Hvhi).
      specialize (Hdiv eq_refl). destruct Hb as [Hbw Hbn]. pose proof Hbw as (_ & _ & Hm & _). rewrite Hm in Hdiv.
      pose proof (div128_bound vb kb Hkb0 Hdiv Hvhi) as HB128.
      pose proof (top65 _ _ (kb + 1) (conj Hbw Hbn) ltac:(lia) Hvhi ltac:(lia)) as Ht65.
      apply bwp_bbind. eapply (BN_add_word_bwp RBL low bs vb [(p, 24)] X0 X);
        [exact H2|exact RBL2|exact (conj Hbw Hbn)|lia|lia|exact HR|eapply Permutation_trans; [exact HP|]; perm_solve|unfold zlength; cbn; lia
        |apply Forall_cons; [cbn; lia|apply Forall_nil]|unfold bsum; cbn -[Z.add Z.mul Z.of_nat]; lia|].
      intros b' X' Hb' Hd' Ht' HP'. cbn [bret ret tree_ops ApLogic.bwp fst snd]. split; [exact Hins0|]. split; [exact Hn0'|]. split; [exact Ebn|]. split.
      + unfold OI. rewrite Ebn. split; [apply st2_setbn; exact H2|]. split; [exact Hn0|]. split; [exact Hkb0|]. split; [exact Hout|]. split; [exact Hin|].
        rewrite (getbn_setbn_same2 RBL b' bs H2 RBL2). exists (vb + low). split; [exact Hb'|]. split; [lia|]. split; [eapply Permutation_trans; [exact HP'|]; perm_solve|].
        intros _. split; [exact Hshr|]. lia.
      + split; [|intros E; congruence]. intros _. exists p, (vb + low). rewrite ?(getbn_setbn_same2 RBL b' bs H2 RBL2). split; [reflexivity|]. split; [exact Hb'|]. lia.
    - cbn. destruct (Hin Hins0 eq_refl) as [Hl1 Hl2].
      pose proof (lor_lt_pow2 (o_l st0) low 64 ltac:(lia) ltac:(lia)) as L1.
      pose proof (lor_lt_pow2 (o_l st0) low (7 * (kb + 1)) ltac:(lia) ltac:(split; [lia|]; eapply Z.lt_le_trans; [|apply (pow7_mono 1 (kb + 1)); lia]; cbn; lia)) as L2.
      split; [reflexivity|]. split; [exact Hn0'|]. split; [reflexivity|]. split; [|split; [intros E; discriminate E|intros _; split; reflexivity]].
      unfold OI; cbn. split; [exact H2|]. split; [exact Hn0|]. split; [exact Hkb0|]. split; [intros E; discriminate E|]. split; [intros _ _; lia|].
      destruct blp as [p|]; [|exact Hblp]. destruct Hblp as (vb & Hb & Hdm & HP & _). exists vb. split; [exact Hb|]. split; [exact Hdm|]. split; [exact HP|]. intros E; discriminate E. }
  eapply bwp_mono; [exact ACC|]. intros [st1 bs1] X1 (Hins1 & Hn1 & Hbn1 & HI1 & Hbnx & Hnbn). cbn [fst snd] in *.
  destruct (negb (Z.land c 128 =? 0)) eqn:Econt; cbn [negb].
  - (* [comment removed for export] *)
    apply bwp_bbind.
    assert (SW : bwp ((if negb (o_bn st1) && (ULONG_MAX_SHR7 <? o_l st1) then
                         bbind ops (match blp with
                                    | None => bbind ops (BN_new ops RBL) (fun p => bret ops (Some p))
                                    | Some p => bret ops (Some p)
                                    end)
                         (fun blp' => bbind ops (BN_set_word ops RBL (o_l st1)) (fun _ => bret ops (mkO2T (o_l st1) true true (o_first st1) (o_n st1), blp')))
                       else bret ops (st1, blp)) bs1) X1
       (fun r X' => o_insub (fst (fst r)) = true /\ o_n (fst (fst r)) = o_n st /\
          (o_bn (fst (fst r)) = true -> st2 (snd r) /\ exists p vb, snd (fst r) = Some p /\ bnv (getbn RBL (snd r)) vb /\ bdm (getbn RBL (snd r)) <= 66 /\
               Permutation X' ((p, 24) :: bnb (getbn RBL (snd r)) ++ X0) /\ ULONG_MAX_SHR7 < o_l (fst (fst r)) /\ 2 ^ 57 <= vb /\ vb < 2 ^ (7 * (kb + 1))) /\
          (o_bn (fst (fst r)) = false -> fst (fst r) = st1 /\ snd (fst r) = blp /\ snd r = bs1 /\ X' = X1))).
    { destruct HI1 as (H2' & Hn0'' & _ & Hout1 & Hin1 & Hblp1).
      destruct (o_bn st1) eqn:Ebn1; cbn [negb andb].
      - (* [comment removed for export] *)
        cbn [bret ret tree_ops ApLogic.bwp fst snd]. split; [exact Hins1|]. split; [exact Hn1|]. split; [|intros E; congruence]. intros _.
        split; [exact H2'|]. destruct (Hbnx eq_refl) as (p & vb & Eblp & Hb & Hvlo & Hvhi). subst blp.
        destruct Hblp1 as (vb' & Hb' & Hdm & HP & Hx). destruct (Hx eq_refl) as (Hshr & _ & _).
        assert (Evb : vb' = vb). { destruct Hb as ((_ & _ & M & _) & _). destruct Hb' as ((_ & _ & M' & _) & _). congruence. } subst vb'.
        exists p, vb. repeat (split; [first [reflexivity|assumption]|]). exact Hvhi.
      - destruct (Z.ltb_spec ULONG_MAX_SHR7 (o_l st1)) as [Hsw|Hsw].
        + (* [comment removed for export] *)
          destruct (Hin1 Hins1 eq_refl) as [Hl1 Hl2]. rewrite ULONG_MAX_SHR7_eq in Hsw.
          apply bwp_bbind.
          assert (NEWP : bwp (match blp with
                              | None => bbind ops (BN_new ops RBL) (fun p => bret ops (Some p))
                              | Some p => bret ops (Some p)
                              end bs1) X1
                   (fun r X' => exists p, fst r = Some p /\ st2 (snd r) /\ bnw (getbn RBL (snd r)) (bn_mag (getbn RBL (snd r))) /\ bdm (getbn RBL (snd r)) <= 66 /\
                                 Permutation X' (bnb (getbn RBL (snd r)) ++ [(p, 24)] ++ X0))).
          { destruct blp as [p|].
            - cbn [bret ret tree_ops ApLogic.bwp fst snd]. destruct Hblp1 as (vb & Hb & Hdm & HP & _). exists p. split; [reflexivity|]. split; [exact H2'|].
              destruct Hb as [Hbw Hbn]. pose proof Hbw as (_ & _ & M & _). rewrite M. split; [exact Hbw|]. split; [exact Hdm|]. eapply Permutation_trans; [exact HP|]. perm_solve.
            - destruct Hblp1 as [_ HP]. apply bwp_bbind. eapply (BN_new_bwp RBL bs1 [] X0 X1); [exact H2'|exact RBL2|exact HR|exact HP|unfold zlength; cbn; lia|apply Forall_nil|unfold bsum; cbn; lia|].
              intros p X' HP'. cbn [bret ret tree_ops ApLogic.bwp fst snd]. exists p. split; [reflexivity|]. split; [apply st2_setbn; exact H2'|].
              rewrite (getbn_setbn_same2 RBL _ bs1 H2' RBL2). split; [exact (bnv_w _ _ bnv_nil)|]. split; [unfold bdm; cbn; lia|]. cbn. exact HP'. }
          eapply bwp_mono; [exact NEWP|]. intros [blp' bs'] X' (p & -> & H2'' & Hbw & Hdm & HP'). cbn [fst snd] in *.
          apply bwp_bbind. eapply (BN_set_word_bwp RBL (o_l st1) bs' _ [(p, 24)] X0 X');
            [exact H2''|exact RBL2|exact Hbw|lia|exact HR|exact HP'|unfold zlength; cbn; lia|apply Forall_cons; [cbn; lia|apply Forall_nil]|unfold bsum; cbn -[Z.add Z.mul]; lia|].
          intros b' X'' Hb' Hd' Ht' HP''. cbn [bret ret tree_ops ApLogic.bwp fst snd].
          split; [reflexivity|]. split; [exact Hn1|]. split; [|intros E; discriminate E]. intros _. split; [apply st2_setbn; exact H2''|].
          exists p, (o_l st1). rewrite (getbn_setbn_same2 RBL b' bs' H2'' RBL2). split; [reflexivity|]. split; [exact Hb'|]. split; [lia|].
          split; [eapply Permutation_trans; [exact HP''|]; perm_solve|]. rewrite ULONG_MAX_SHR7_eq. cbn [o_l]. lia.
        + cbn [bret ret tree_ops ApLogic.bwp fst snd]. split; [exact Hins1|]. split; [exact Hn1|]. split; [intros E; congruence|]. intros _. repeat split; reflexivity. }
    eapply bwp_mono; [exact SW|]. intros [[st2 blp2] bs2] X2 (Hins2 & Hn2 & HbnT & HbnF). cbn [fst snd] in *.
    destruct (o_bn st2) eqn:Ebn2.
    + (* [comment removed for export] *)
      destruct (HbnT eq_refl) as (H2' & p & vb & -> & Hb & Hdm & HP & Hshr & Hvlo & Hvhi). clear HbnF.
      pose proof (top65 _ _ (kb + 1) Hb ltac:(lia) Hvhi ltac:(lia)) as Ht65.
      apply bwp_bbind. eapply (BN_lshift_bwp RBL 7 bs2 vb [(p, 24)] X0 X2);
        [exact H2'|exact RBL2|exact Hb|lia|lia|exact HR|eapply Permutation_trans; [exact HP|]; perm_solve|unfold zlength; cbn; lia
        |apply Forall_cons; [cbn; lia|apply Forall_nil]|unfold bsum; cbn -[Z.add Z.mul Z.of_nat]; lia|].
      intros b' X' Hb' Hd' Ht' HP'. cbn [fst snd].
      assert (Hvhi' : vb * 2 ^ 7 < 2 ^ (7 * (kb + 1 + 1))).
      { replace (7 * (kb + 1 + 1)) with (7 * (kb + 1) + 7) by lia. rewrite Z.pow_add_r by lia. pose proof (Z.pow_pos_nonneg 2 7 ltac:(lia) ltac:(lia)). nia. }
      eapply bwp_mono; [eapply (IH st2 (Some p) (setbn RBL b' bs2) X' X0 (kb + 1) (tot + 1) HR); try lia|].
      * unfold OI. rewrite Ebn2, Hins2. split; [apply st2_setbn; exact H2'|]. split; [lia|]. split; [lia|]. split; [intros E; discriminate E|]. split; [intros _ E; discriminate E|].
        rewrite (getbn_setbn_same2 RBL b' bs2 H2' RBL2). exists (vb * 2 ^ 7). split; [exact Hb'|]. split; [lia|]. split; [eapply Permutation_trans; [exact HP'|]; perm_solve|].
        intros _. split; [exact Hshr|]. split; [change (2 ^ 7) with 128; lia|exact Hvhi'].
      * intros _. rewrite (getbn_setbn_same2 RBL b' bs2 H2' RBL2). destruct Hb' as ((_ & _ & M & _) & _). rewrite M. exists vb. change (2 ^ 7) with 128. lia.
      * intros [[res blp3] bs3] X3 [HE HB]. cbn [fst snd] in *. split; [exact HE|]. destruct res; [rewrite zl_cons; lia|exact I].
    + (* [comment removed for export] *)
      destruct (HbnF eq_refl) as (-> & -> & -> & ->). clear HbnT.
      destruct HI1 as (H2' & _ & _ & _ & Hin1 & Hblp1). destruct (Hin1 Hins1 Ebn2) as [Hl1 Hl2].
      rewrite Z.shiftl_mul_pow2 by lia. pose proof (land_mask64 (o_l st1 * 2 ^ 7) ltac:(lia)) as [M1 M2].
      assert (Hl3 : o_l st1 * 2 ^ 7 < 2 ^ (7 * (kb + 1 + 1))).
      { replace (7 * (kb + 1 + 1)) with (7 * (kb + 1) + 7) by lia. rewrite Z.pow_add_r by lia. pose proof (Z.pow_pos_nonneg 2 7 ltac:(lia) ltac:(lia)). nia. }
      eapply bwp_mono; [eapply (IH _ blp bs1 X1 X0 (kb + 1) (tot + 1) HR); try (cbn; lia); try (intros E; discriminate E)|].
      * unfold OI; cbn. split; [exact H2'|]. split; [lia|]. split; [lia|]. split; [intros E; discriminate E|]. split; [intros _ _; lia|].
        destruct blp as [p|]; [|split; [reflexivity|exact (proj2 Hblp1)]].
        destruct Hblp1 as (vb & Hb & Hdm & HP & _). exists vb. split; [exact Hb|]. split; [exact Hdm|]. split; [exact HP|]. intros E; discriminate E.
      * intros [[res blp3] bs3] X3 [HE HB]. cbn [fst snd] in *. split; [exact HE|]. destruct res; [rewrite zl_cons; lia|exact I].
  - (* [comment removed for export] *)
    apply bwp_bbind. eapply bwp_mono; [eapply (o2t_emit_bwp st1 blp bs1 X1 X0 kb HR HI1 Hins1 ltac:(lia) Hbnx)|].
    intros [[st2 blp2] bs2] X2 (HI2 & Hins2 & Hbn2 & Eb & Hn2). cbn [fst snd] in *. subst blp2.
    eapply bwp_mono; [eapply (IH st2 blp bs2 X2 X0 0 (tot + 1) HR HI2); try lia; intros E; rewrite Hbn2 in E; discriminate E|].
    intros [[res blp3] bs3] X3 [HE HB]. cbn [fst snd] in *. split; [exact HE|]. destruct res; [rewrite zl_cons; lia|exact I].
Qed.

Lemma st2_abs0 : st2 (abs0 (ptr:=ptr)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Theorem obj2txt_num_bwp0 : forall content X,
  roomy0 X -> 1 <= zlength content <= 586 ->
  bwp (tbind (obj2txt_num ops content abs0) (fun p => TRet (fst p))) X (fun n X' => Permutation X' X /\ -1 <= n <= 5 * 586).
Proof.
  intros content X HR Hlen. apply bwp_bind. unfold obj2txt_num. apply bwp_bbind.
  eapply bwp_mono; [eapply (o2t_bytes_bwp content o2t_init None abs0 X X 0 0 HR); try (cbn; lia); try (intros E; discriminate E)|].
  { unfold OI, o2t_init; cbn. split; [exact st2_abs0|]. split; [lia|]. split; [lia|]. split; [intros _; split; reflexivity|]. split; [intros E; discriminate E|].
    split; [reflexivity|apply Permutation_refl]. }
  intros [[res blp] bs'] X' [HE HB]. cbn [fst snd] in *. destruct HE as [H2' Hblp].
  apply bwp_bbind.
  assert (FR : bwp (match blp with Some p => BN_free ops RBL (Some p) | None => bret ops tt end bs') X' (fun r X'' => Permutation X'' X)).
  { destruct blp as [p|].
    - destruct Hblp as (vb & Hb & HP). eapply (BN_free_bwp RBL bs' p vb [] X X'); [exact H2'|exact RBL2|exact Hb| |intros X'' HP''; exact HP''].
      eapply Permutation_trans; [exact HP|]. cbn [app]. apply Permutation_refl.
    - cbn. exact Hblp. }
  eapply bwp_mono; [exact FR|]. intros [[] bs''] X'' HP''. cbn [fst snd].
  destruct res as [n|]; cbn; (split; [exact HP''|lia]).
Qed.
End O2T.
