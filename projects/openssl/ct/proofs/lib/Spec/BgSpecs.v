(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnInv BgState BgLib BgInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Specs.
Context {ptr : Type}.
Local Notation ST := (bstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition slots_same (u : nat) (outs : list bnref) (s s' : ST) : Prop :=
  forall r, (r < NFIX + u)%nat -> ~ In r outs -> getbn r s' = getbn r s.

Definition scal_same (s s' : ST) : Prop :=
  st_ri s' = st_ri s /\ st_n0 s' = st_n0 s /\ st_rbits s' = st_rbits s /\ st_rshift s' = st_rshift s.

Definition ctx_keep (s s' : ST) : Prop :=
  (length (st_bns s) <= length (st_bns s'))%nat /\
  gx_used (st_ctx s') = gx_used (st_ctx s) /\ gx_frames (st_ctx s') = gx_frames (st_ctx s).

Definition keeps0 (u : nat) (outs : list bnref) (s s' : ST) : Prop := ctx_keep s s' /\ slots_same u outs s s'.
Definition keeps (u : nat) (outs : list bnref) (s s' : ST) : Prop := keeps0 u outs s s' /\ scal_same s s'.

Lemma slots_same_refl : forall u outs s, slots_same u outs s s.
Proof. unfold slots_same. intros u outs s r _ _. reflexivity. Qed.

Lemma slots_same_trans : forall u o1 o2 s s1 s2,
  slots_same u o1 s s1 -> slots_same u o2 s1 s2 -> slots_same u (o1 ++ o2) s s2.
Proof.
  unfold slots_same. intros u o1 o2 s s1 s2 H1 H2 r Hr Hn. rewrite H2, H1; try assumption; try reflexivity; intros Hin; apply Hn, in_or_app; auto.
Qed.

(* [comment removed for export] *)
Lemma slots_same_weaken : forall u u' o o' s s',
  (u' <= u)%nat -> (forall r, In r o -> (r < NFIX + u')%nat -> In r o') -> slots_same u o s s' -> slots_same u' o' s s'.
Proof. unfold slots_same. intros u u' o o' s s' Hu Ho H r Hr Hn. apply H; [lia|]. intros Hin. apply Hn, Ho; assumption. Qed.

Lemma slots_same_setbn : forall u r b (s : ST), slots_same u [r] s (setbn r b s).
Proof. unfold slots_same. intros u r b s r' _ Hn. apply getbn_setbn_other. intros ->. apply Hn. left. reflexivity. Qed.

Lemma scal_same_refl : forall s, scal_same s s.
Proof. intros s. unfold scal_same. tauto. Qed.

Lemma scal_same_trans : forall s s1 s2, scal_same s s1 -> scal_same s1 s2 -> scal_same s s2.
Proof. intros s s1 s2 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold scal_same. repeat split; congruence. Qed.

Lemma ctx_keep_refl : forall s, ctx_keep s s.
Proof. intros s. unfold ctx_keep. auto. Qed.

Lemma ctx_keep_trans : forall s s1 s2, ctx_keep s s1 -> ctx_keep s1 s2 -> ctx_keep s s2.
Proof. intros s s1 s2 (A1 & A2 & A3) (B1 & B2 & B3). unfold ctx_keep. repeat split; try congruence. lia. Qed.

Lemma keeps_refl : forall u outs s, keeps u outs s s.
Proof. intros. split; [split|]; [apply ctx_keep_refl|apply slots_same_refl|apply scal_same_refl]. Qed.

Lemma keeps_trans : forall u o1 o2 s s1 s2, keeps u o1 s s1 -> keeps u o2 s1 s2 -> keeps u (o1 ++ o2) s s2.
Proof.
  intros u o1 o2 s s1 s2 [[A1 A2] A3] [[B1 B2] B3]. split; [split|].
  - eapply ctx_keep_trans; eassumption.
  - eapply slots_same_trans; eassumption.
  - eapply scal_same_trans; eassumption.
Qed.

Lemma keeps_weaken : forall u u' o o' s s',
  (u' <= u)%nat -> (forall r, In r o -> (r < NFIX + u')%nat -> In r o') -> keeps u o s s' -> keeps u' o' s s'.
Proof. intros u u' o o' s s' Hu Ho [[A1 A2] A3]. split; [split|]; try assumption. eapply slots_same_weaken; eassumption. Qed.

Lemma keeps_setbn : forall u r b (s : ST), keeps u [r] s (setbn r b s).
Proof.
  intros u r b s. split; [split|].
  - unfold ctx_keep. rewrite length_setbn. auto.
  - apply slots_same_setbn.
  - unfold scal_same. repeat split; reflexivity.
Qed.

Lemma keeps0_of_keeps : forall u o s s', keeps u o s s' -> keeps0 u o s s'.
Proof. intros u o s s' [H _]. exact H. Qed.

Lemma keeps_used : forall u o s s', keeps u o s s' -> gx_used (st_ctx s') = gx_used (st_ctx s).
Proof. intros u o s s' [[(_ & H & _) _] _]. exact H. Qed.

Lemma keeps_frames : forall u o s s', keeps u o s s' -> gx_frames (st_ctx s') = gx_frames (st_ctx s).
Proof. intros u o s s' [[(_ & _ & H) _] _]. exact H. Qed.

Lemma keeps_get : forall u o s s' r, keeps u o s s' -> (r < NFIX + u)%nat -> ~ In r o -> getbn r s' = getbn r s.
Proof. intros u o s s' r [[_ H] _] Hr Hn. apply H; assumption. Qed.

Lemma keeps_live : forall u o s s' r, keeps u o s s' -> live r s -> live r s'.
Proof. intros u o s s' r H Hl. unfold live in *. rewrite (keeps_used _ _ _ _ H). exact Hl. Qed.

(* [comment removed for export] *)
Definition upd1 (r : bnref) (s : ST) (P : BN -> Prop) : unit -> ST -> Prop :=
  fun _ s' => exists b', s' = setbn r b' s /\ P b'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hoare_bind_get : forall {B} r (f : BN -> BM B) F s Q,
  hoare F s (f (getbn r s)) Q -> hoare F s (bbind ops (bget ops r) f) Q.
Proof. intros B r f F s Q H. exact H. Qed.

Lemma hoare_bind_getst : forall {B} (f : ST -> BM B) F s Q,
  hoare F s (f s) Q -> hoare F s (bbind ops (bgetst ops) f) Q.
Proof. intros B f F s Q H. exact H. Qed.

Lemma hoare_bind_getctx : forall {B} (f : bg_ctx ptr -> BM B) F s Q,
  hoare F s (f (st_ctx s)) Q -> hoare F s (bbind ops (bgetctx ops) f) Q.
Proof. intros B f F s Q H. exact H. Qed.

Lemma hoare_bind_ret : forall {A B} (a : A) (f : A -> BM B) F s Q,
  hoare F s (f a) Q -> hoare F s (bbind ops (bret ops a) f) Q.
Proof. intros A B a f F s Q H. exact H. Qed.

Lemma hoare_bind_set : forall {B} r b (f : unit -> BM B) F s Q,
  (r < length (st_bns s))%nat -> r <> ROne -> bg_ok b ->
  bn_d b = bn_d (getbn r s) -> length (bn_buf b) = length (bn_buf (getbn r s)) -> bn_flags b = bn_flags (getbn r s) ->
  hoare F (setbn r b s) (f tt) Q -> hoare F s (bbind ops (bset ops r b) f) Q.
Proof.
  intros B r b f F s Q Hr Hn Hb Ed El Ef H. eapply hoare_bind; [apply hoare_set with (Q := fun _ s' => s' = setbn r b s); try assumption; reflexivity|].
  intros [] s' _ ->. exact H.
Qed.

Lemma hoare_bind_setmont : forall {B} ri n0 (f : unit -> BM B) F s Q,
  hoare F (set_mont ri n0 s) (f tt) Q -> hoare F s (bbind ops (bsetmont ops ri n0) f) Q.
Proof.
  intros B ri n0 f F s Q H. eapply hoare_bind; [apply hoare_setmont with (Q := fun _ s' => s' = set_mont ri n0 s); reflexivity|].
  intros [] s' _ ->. exact H.
Qed.

Lemma hoare_bind_setrecp : forall {B} bits sh (f : unit -> BM B) F s Q,
  hoare F (set_recp bits sh s) (f tt) Q -> hoare F s (bbind ops (bsetrecp ops bits sh) f) Q.
Proof.
  intros B bits sh f F s Q H. eapply hoare_bind; [apply hoare_setrecp with (Q := fun _ s' => s' = set_recp bits sh s); reflexivity|].
  intros [] s' _ ->. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition gexpanded (b : BN) (words : nat) (b' : BN) : Prop :=
  bn_top b' = bn_top b /\ bn_neg b' = bn_neg b /\ bn_flags b' = bn_flags b /\
  bn_buf b' = (if (words <=? bn_dmax b)%nat then bn_buf b
               else firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)) /\
  bg_ok b' /\ (words <= bn_dmax b')%nat /\ (bn_dmax b <= bn_dmax b')%nat.

Lemma gexpanded_prefix : forall (b b' : BN) words, bg_ok b -> gexpanded b words b' ->
  firstn (bn_top b) (bn_buf b') = firstn (bn_top b) (bn_buf b).
Proof.
  intros b b' words (_ & Ht & _) (_ & _ & _ & Eb & _). rewrite Eb.
  destruct (Nat.leb_spec words (bn_dmax b)); [reflexivity|].
  rewrite firstn_app, firstn_firstn, Nat.min_id, firstn_length_le by (unfold bn_dmax in Ht; exact Ht).
  rewrite Nat.sub_diag. cbn [firstn]. apply app_nil_r.
Qed.

Lemma bn_wexpand_spec : forall r words F s,
  (r < length (st_bns s))%nat -> r <> ROne -> Z.of_nat words <= BG_DMAX ->
  hoare F s (bn_wexpand ops r words) (upd1 r s (gexpanded (getbn r s) words)).
Proof.
  intros r words F s Hr Hn Hw. apply hoare_wf. intros Hs. unfold bn_wexpand.
  apply hoare_bind_get. set (b := getbn r s) in *.
  pose proof (st_wf_ok r s Hs Hr Hn) as Hb. fold b in Hb. pose proof Hb as (Hb1 & Hb2 & Hb3 & Hb4).
  destruct (Nat.leb_spec words (bn_dmax b)) as [Hle|Hgt].
  - apply hoare_ret. exists b. split; [unfold b; rewrite setbn_getbn_id; reflexivity|].
    unfold gexpanded. destruct (Nat.leb_spec words (bn_dmax b)); [|lia]. repeat split; try reflexivity; try assumption; lia.
  - destruct (Z.ltb_spec BN_WORDS_MAX (Z.of_nat words)) as [Hbig|_]; [unfold BN_WORDS_MAX, BG_DMAX in *; lia|].
    destruct (Z.ltb_spec 512 (Z.of_nat words)) as [Hbig|_]; [unfold BG_DMAX in *; lia|].
    assert (Ef1 : has_flag b BN_FLG_STATIC_DATA = false) by (unfold has_flag; destruct Hb4 as [-> | ->]; reflexivity).
    assert (Ef2 : has_flag b BN_FLG_SECURE = false) by (unfold has_flag; destruct Hb4 as [-> | ->]; reflexivity).
    rewrite Ef1, Ef2.
    (* [comment removed for export] *)
    intros X Hs' Hfl (HP & HF & HFs). cbn [bbind bmalloc bind lib_malloc tree_ops tbind gwp ret unreachable].
    split; [eapply own_ok_bg; [exact Hs|split; [exact HP|split; assumption]|unfold BG_BSZ, BG_DMAX in *; lia]|].
    split; [reflexivity|]. intros p Hp.
    destruct (blocks_setbn r s Hr) as (R & HR1 & HR2). fold b in HR1.
    set (bn := mkBN (Some p) (firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)) (bn_top b) (bn_neg b) (bn_flags b)).
    assert (Hlen : length (firstn (bn_top b) (bn_buf b) ++ repeat 0 (words - bn_top b)) = words).
    { rewrite length_app, firstn_length_le, repeat_length by exact Hb2. unfold bn_dmax in *. lia. }
    assert (Hbn : bg_ok bn).
    { unfold bg_ok, bn_dmax. subst bn. cbn [bn_buf bn_top bn_flags]. rewrite Hlen.
      split; [apply limbs_app; [apply limbs_firstn; exact Hb1|apply limbs_repeat; exact limb_0]|].
      split; [unfold bn_dmax in *; lia|]. split; [exact Hw|exact Hb4]. }
    assert (Hfin : st_wf (setbn r bn s) /\ fl_ok (setbn r bn s) /\ own (setbn r bn s) F ((p, 8 * Z.of_nat words) :: R ++ F) /\
                   upd1 r s (gexpanded b words) tt (setbn r bn s)).
    { split; [apply st_wf_setbn; assumption|]. split; [apply fl_ok_setbn; [exact Hfl|reflexivity]|]. split.
      - split; [|split; assumption]. specialize (HR2 bn). unfold bn_blocks at 1 in HR2. subst bn. cbn [bn_d] in HR2.
        unfold bn_dmax in HR2. cbn [bn_buf] in HR2. rewrite Hlen in HR2.
        apply Permutation_sym. eapply Permutation_trans; [apply Permutation_app_tail; exact HR2|]. apply Permutation_refl.
      - exists bn. split; [reflexivity|]. unfold gexpanded. destruct (Nat.leb_spec words (bn_dmax b)); [lia|].
        assert (Hd' : bn_dmax bn = words) by (unfold bn_dmax; subst bn; cbn [bn_buf]; exact Hlen).
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [exact Hbn|]. rewrite Hd'. lia. }
    assert (HPX : Permutation ((p, 8 * Z.of_nat words) :: X) ((p, 8 * Z.of_nat words) :: bn_blocks b ++ R ++ F)).
    { apply perm_skip. eapply Permutation_trans; [exact HP|]. rewrite app_assoc. apply Permutation_app_tail. exact HR1. }
    destruct (bn_d b) as [q|] eqn:Ed; unfold bn_blocks in HPX; rewrite Ed in HPX; cbn [bfree_opt bfree bret bind lib_free tree_ops tbind gwp ret bset fst snd app] in *.
    + exists (8 * Z.of_nat (bn_dmax b)), ((p, 8 * Z.of_nat words) :: R ++ F). split; [|exact Hfin].
      eapply Permutation_trans; [exact HPX|]. apply perm_swap.
    + destruct Hfin as (W1 & W0 & (W2 & W3) & W4). split; [exact W1|]. split; [exact W0|]. split; [|exact W4]. split; [|exact W3].
      eapply Permutation_trans; [exact HPX|exact W2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nondecr_app_inv : forall l l', nondecr (l ++ l') -> nondecr l /\ nondecr l'.
Proof.
  induction l as [|x l IH]; intros l' H; cbn [app] in *; [split; [exact I|exact H]|].
  cbn [nondecr] in H. destruct H as [H1 H2]. destruct (IH l' H2) as [A B]. split; [|exact B].
  cbn [nondecr]. split; [|exact A]. destruct l as [|y l]; [exact I|]. cbn [app] in H1. exact H1.
Qed.

Lemma nondecr_snoc : forall l x y, nondecr (l ++ [x]) -> (x <= y)%nat -> nondecr (l ++ [x; y]).
Proof.
  induction l as [|z l IH]; intros x y H Hxy; cbn [app nondecr] in *; [tauto|].
  destruct H as [H1 H2]. split; [|apply IH; assumption]. destruct l as [|w l]; cbn [app] in *; assumption.
Qed.

Lemma nondecr_last_two : forall l x y, nondecr (l ++ [x; y]) -> (x <= y)%nat.
Proof.
  induction l as [|z l IH]; intros x y H; cbn [app nondecr] in *; [tauto|]. destruct H as [_ H]. apply IH. exact H.
Qed.

Lemma nondecr_drop_last : forall l x y, nondecr (l ++ [x; y]) -> nondecr (l ++ [x]).
Proof.
  intros l x y H. replace (l ++ [x; y]) with ((l ++ [x]) ++ [y]) in H by (rewrite <- app_assoc; reflexivity).
  apply nondecr_app_inv in H. tauto.
Qed.

Lemma nondecr_set_last : forall l x y, nondecr (l ++ [x]) -> (x <= y)%nat -> nondecr (l ++ [y]).
Proof.
  induction l as [|z l IH]; intros x y H Hxy; cbn [app nondecr] in *; [tauto|].
  destruct H as [H1 H2]. split; [|eapply IH; eassumption]. destruct l as [|w l]; cbn [app] in *; [lia|assumption].
Qed.

Lemma perm_ins : forall (x : ptr * Z) A B C, Permutation (x :: A ++ B ++ C) (A ++ B ++ x :: C).
Proof. intros. rewrite !app_assoc. apply Permutation_middle. Qed.

(* [comment removed for export] *)
Lemma hoare_bind_setctx : forall {B} c (f : unit -> BM B) F s Q,
  (st_wf s -> ctx_wf c) -> gx_items c = gx_items (st_ctx s) -> gx_indexes c = gx_indexes (st_ctx s) ->
  hoare F (set_ctx c s) (f tt) Q -> hoare F s (bbind ops (bsetctx ops c) f) Q.
Proof.
  intros B c f F s Q Hc Ei Ex H. eapply hoare_bind with (R := fun _ s' => s' = set_ctx c s).
  - intros X Hs Hfl (HP & HF). cbn. split; [|split; [apply fl_ok_set_ctx; exact Hfl|split; [|reflexivity]]].
    + destruct Hs as (E & Hok & Hone & Hcw). unfold st_wf. cbn [set_ctx st_bns st_ctx]. rewrite Ei.
      split; [exact E|]. split; [exact Hok|]. split; [exact Hone|]. apply Hc. unfold st_wf. auto.
    + split; [|exact HF]. unfold blocks_of. cbn [set_ctx st_bns st_ctx]. rewrite Ei, Ex. exact HP.
  - intros [] s' _ ->. exact H.
Qed.

Lemma BN_CTX_start_spec : forall F s,
  (length (gx_frames (st_ctx s)) < BG_DEPTH)%nat ->
  hoare F s (BN_CTX_start ops) (fun _ s' =>
     st_bns s' = st_bns s /\ scal_same s s' /\ gx_used (st_ctx s') = gx_used (st_ctx s) /\
     gx_frames (st_ctx s') = gx_frames (st_ctx s) ++ [gx_used (st_ctx s)]).
Proof.
  intros F s Hd. apply hoare_wf. intros Hs. pose proof Hs as (E & Hok & Hone & Hcw).
  destruct Hcw as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
  unfold BN_CTX_start. apply hoare_bind_getctx. set (c := st_ctx s) in *.
  rewrite W1, W2. cbn [Nat.eqb negb orb].
  destruct W8 as [(S1 & S2 & S3)|(S1 & S2 & S3)].
  - (* [comment removed for export] *)
    rewrite S1, S2. cbn [length Nat.eqb negb app].
    intros X Hs' Hfl (HP & HF & HFs). cbn [bbind bmalloc bind lib_malloc tree_ops tbind gwp ret unreachable].
    split; [eapply own_ok_bg; [exact Hs|split; [exact HP|split; assumption]|unfold BG_BSZ, BN_CTX_START_FRAMES; lia]|].
    split; [reflexivity|]. intros p Hp. rewrite S3. cbn [bfree_opt bret bsetctx bind tree_ops tbind gwp ret fst snd].
    split; [|split; [apply fl_ok_set_ctx; exact Hfl|split]].
    + unfold st_wf. cbn [set_ctx st_bns st_ctx gx_items]. split; [exact E|]. split; [exact Hok|]. split; [exact Hone|].
      unfold ctx_wf. cbn [gx_err_stack gx_too_many gx_pused gx_used gx_items gx_current gx_frames gx_ssize gx_indexes].
      repeat split; try assumption.
      * cbn [app nondecr]. auto.
      * right. split; [reflexivity|]. split; [discriminate|]. cbn. unfold BG_DEPTH. lia.
    + split; [|split; assumption]. unfold blocks_of. cbn [set_ctx st_bns st_ctx gx_items gx_indexes opt_block].
      unfold blocks_of in HP. fold c in HP. rewrite S3 in HP. cbn [opt_block] in HP. rewrite app_nil_r in HP.
      eapply Permutation_trans; [apply perm_skip; exact HP|].
      rewrite <- !app_assoc. cbn [app]. apply perm_ins.
    + cbn [set_ctx st_bns st_ctx gx_used gx_frames]. split; [reflexivity|]. split; [unfold scal_same; repeat split; reflexivity|].
      split; reflexivity.
  - assert (Ed : (length (gx_frames c) =? gx_ssize c)%nat = false) by (apply Nat.eqb_neq; rewrite S1; lia).
    rewrite Ed.
    apply hoare_bind_setctx with (f := fun _ => bret ops tt).
    + intros _. unfold ctx_wf. cbn [gx_err_stack gx_too_many gx_pused gx_used gx_items gx_current gx_frames gx_ssize gx_indexes].
      repeat split; try assumption.
      * rewrite <- app_assoc. cbn [app]. apply nondecr_snoc; [exact W7|lia].
      * right. split; [exact S1|]. split; [exact S2|]. rewrite length_app. cbn [length]. unfold BG_DEPTH in *. lia.
    + reflexivity.
    + reflexivity.
    + apply hoare_ret. cbn [set_ctx st_bns st_ctx gx_used gx_frames]. split; [reflexivity|]. split; [unfold scal_same; repeat split; reflexivity|].
      split; reflexivity.
Qed.

Lemma bg_ok_zero : forall b : BN, bg_ok b -> bg_ok (bn_zero_pure b).
Proof. intros b (H1 & H2 & H3 & H4). unfold bg_ok, bn_zero_pure, bn_dmax in *. cbn [bn_buf bn_top bn_flags]. repeat split; try assumption. lia. Qed.

Lemma getbn_app_l : forall r (l l' : list BN), (r < length l)%nat -> nth r (l ++ l') (bn_nil 0) = nth r l (bn_nil 0).
Proof. intros. apply app_nth1. assumption. Qed.

Lemma nth_repeat_nil : forall r n (l : list BN), (length l <= r)%nat -> nth r (l ++ repeat (bn_nil 0) n) (bn_nil 0) = bn_nil 0.
Proof.
  intros r n l Hr. rewrite app_nth2 by lia. destruct (Nat.lt_ge_cases (r - length l) n) as [Hlt|Hge].
  - apply nth_repeat_lt. exact Hlt.
  - apply nth_overflow. rewrite repeat_length. lia.
Qed.

Lemma concat_blocks_repeat_nil : forall n, concat (map bn_blocks (repeat (bn_nil 0 : BN) n)) = [].
Proof. induction n as [|n IH]; cbn [repeat map concat]; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pool_cur_next : forall u : nat,
  (if (u =? 0)%nat then Some 0%nat
   else if (u mod 16 =? 0)%nat then match (if (u =? 0)%nat then None else Some ((u - 1) / 16)%nat) with Some k => Some (S k) | None => None end
        else (if (u =? 0)%nat then None else Some ((u - 1) / 16)%nat)) = Some (u / 16)%nat.
Proof.
  intros u. destruct (Nat.eqb_spec u 0) as [->|Hu]; [reflexivity|].
  pose proof (Nat.div_mod_eq u 16). pose proof (Nat.mod_upper_bound u 16 ltac:(lia)).
  pose proof (Nat.div_mod_eq (u - 1) 16). pose proof (Nat.mod_upper_bound (u - 1) 16 ltac:(lia)).
  destruct (Nat.eqb_spec (u mod 16) 0) as [Em|Em]; f_equal; lia.
Qed.

Lemma BN_CTX_get_spec : forall F s,
  (gx_used (st_ctx s) < BG_POOL)%nat ->
  hoare F s (BN_CTX_get ops) (fun a s' =>
     a = RPool (gx_used (st_ctx s)) /\ gx_used (st_ctx s') = S (gx_used (st_ctx s)) /\
     gx_frames (st_ctx s') = gx_frames (st_ctx s) /\ scal_same s s' /\
     (length (st_bns s) <= length (st_bns s'))%nat /\
     (forall r, r <> a -> getbn r s' = getbn r s) /\
     bn_top (getbn a s') = 0%nat /\ bn_neg (getbn a s') = false).
Proof.
  intros F s Hu X Hs Hfl (HP & HF & HFs). pose proof Hs as (E & Hok & Hone & Hcw).
  destruct Hcw as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
  unfold BN_CTX_get. set (c := st_ctx s) in *. set (u := gx_used c) in *.
  cbn [bbind bgetctx bind tree_ops tbind ret fst snd]. fold c. rewrite W1, W2, W3. cbn [Nat.eqb negb orb]. fold u.
  destruct (Nat.eqb_spec u (BN_CTX_POOL_SIZE * length (gx_items c))) as [Efull|Hnf].
  - (* [comment removed for export] *)
    destruct (Nat.leb_spec 3 (length (gx_items c))) as [H3|H3]; [exfalso; unfold BG_POOL, BN_CTX_POOL_SIZE in *; lia|].
    cbn [bbind bmalloc bind lib_malloc tree_ops tbind gwp ret unreachable].
    split; [eapply own_ok_bg; [exact Hs|split; [exact HP|split; assumption]|unfold BG_BSZ, POOL_ITEM_BYTES; lia]|].
    split; [reflexivity|]. intros p Hp.
    cbn [bgetst bgetctx bsetbns bsetctx bget bset bret bbind bind tree_ops tbind gwp ret fst snd].
    match goal with |- st_wf ?sf /\ _ => set (sfin := sf) end.
    enough (HH : st_wf sfin /\ own sfin F ((p, POOL_ITEM_BYTES) :: X) /\
      (RPool u = RPool u /\ gx_used (st_ctx sfin) = S u /\ gx_frames (st_ctx sfin) = gx_frames c /\ scal_same s sfin /\
       (length (st_bns s) <= length (st_bns sfin))%nat /\ (forall r : nat, r <> RPool u -> getbn r sfin = getbn r s) /\
       bn_top (getbn (RPool u) sfin) = 0%nat /\ bn_neg (getbn (RPool u) sfin) = false)).
    { destruct HH as (HH1 & HH2 & HH3). split; [exact HH1|]. split; [|split; [exact HH2|exact HH3]].
      unfold sfin. apply fl_ok_setbn; [|reflexivity]. apply fl_ok_set_ctx.
      apply (fl_ok_app_nil s BN_CTX_POOL_SIZE Hfl). rewrite E. lia. }
    set (l1 := st_bns s ++ repeat (bn_nil 0) BN_CTX_POOL_SIZE).
    assert (Hl1 : length l1 = (length (st_bns s) + 16)%nat) by (unfold l1; rewrite length_app, repeat_length; reflexivity).
    assert (Hnil : nth (RPool u) l1 (bn_nil 0) = bn_nil 0) by (unfold l1; apply nth_repeat_nil; unfold RPool; lia).
    assert (Ebns : st_bns sfin = l1).
    { unfold sfin, setbn, set_bns, set_ctx, getbn. cbn [st_bns st_ctx]. fold l1. rewrite Hnil.
      change (bn_zero_pure (bn_nil 0)) with (bn_nil 0 : BN). rewrite <- Hnil at 1. apply list_set_nth_id. }
    assert (Ectx : st_ctx sfin = mkGx (gx_items c ++ [p]) (Some (length (gx_items c))) (S u) (gx_indexes c) (gx_frames c)
                                      (gx_ssize c) (S u) 0 false) by reflexivity.
    assert (Escal : scal_same s sfin) by (unfold scal_same; repeat split; reflexivity).
    clearbody sfin.
    split; [|split].
    + unfold st_wf. rewrite Ebns, Ectx. cbn [gx_items]. rewrite Hl1, length_app. cbn [length].
      split; [unfold BN_CTX_POOL_SIZE in *; lia|]. split; [|split].
      * intros r Hr Hn. unfold getbn. rewrite Ebns. unfold l1.
        destruct (Nat.lt_ge_cases r (length (st_bns s))) as [Hlt|Hge].
        -- rewrite app_nth1 by exact Hlt. apply Hok; assumption.
        -- rewrite nth_repeat_nil by exact Hge. apply bg_ok_nil. left. reflexivity.
      * unfold getbn. rewrite Ebns. unfold l1. rewrite app_nth1 by (rewrite E; unfold ROne, NFIX; lia). exact Hone.
      * unfold ctx_wf. cbn [gx_err_stack gx_too_many gx_pused gx_used gx_items gx_current gx_frames gx_ssize gx_indexes].
        rewrite length_app. cbn [length].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [unfold BN_CTX_POOL_SIZE in *; lia|]. split; [unfold BG_POOL, BN_CTX_POOL_SIZE in *; lia|].
        split; [|split].
        -- cbn [Nat.eqb]. f_equal. replace (S u - 1)%nat with u by lia. rewrite Efull. unfold BN_CTX_POOL_SIZE. rewrite Nat.mul_comm, Nat.div_mul by lia. reflexivity.
        -- eapply nondecr_set_last; [exact W7|lia].
        -- exact W8.
    + split; [|split; assumption]. unfold blocks_of. rewrite Ebns, Ectx. cbn [gx_items gx_indexes]. unfold l1.
      rewrite map_app, concat_app, concat_blocks_repeat_nil, app_nil_r, map_app. cbn [map].
      unfold blocks_of in HP. fold c in HP.
      eapply Permutation_trans; [apply perm_skip; exact HP|].
      rewrite <- !app_assoc. cbn [app]. apply perm_ins.
    + rewrite Ectx, Ebns. cbn [gx_used gx_frames]. unfold getbn. rewrite Ebns.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Escal|].
      split; [rewrite Hl1; lia|]. split; [|split].
      * intros r Hr. unfold l1.
        destruct (Nat.lt_ge_cases r (length (st_bns s))) as [Hlt|Hge]; [apply app_nth1; exact Hlt|].
        rewrite nth_repeat_nil by exact Hge. symmetry. apply nth_overflow. exact Hge.
      * rewrite Hnil. reflexivity.
      * rewrite Hnil. reflexivity.
  - (* [comment removed for export] *)
    assert (Hlt : (u < BN_CTX_POOL_SIZE * length (gx_items c))%nat) by (fold u in W4; lia).
    cbn [bgetst bgetctx bsetbns bsetctx bget bset bret bbind bind tree_ops tbind gwp ret fst snd].
    match goal with |- st_wf ?sf /\ _ => set (sfin := sf) end.
    enough (HH : st_wf sfin /\ own sfin F X /\
      (RPool u = RPool u /\ gx_used (st_ctx sfin) = S u /\ gx_frames (st_ctx sfin) = gx_frames c /\ scal_same s sfin /\
       (length (st_bns s) <= length (st_bns sfin))%nat /\ (forall r : nat, r <> RPool u -> getbn r sfin = getbn r s) /\
       bn_top (getbn (RPool u) sfin) = 0%nat /\ bn_neg (getbn (RPool u) sfin) = false)).
    { destruct HH as (HH1 & HH2 & HH3). split; [exact HH1|]. split; [|split; [exact HH2|exact HH3]].
      unfold sfin. apply fl_ok_set_ctx. apply fl_ok_setbn; [|reflexivity]. apply fl_ok_set_ctx. exact Hfl. }
    assert (Hr : (RPool u < length (st_bns s))%nat) by (unfold RPool; lia).
    assert (Hn : RPool u <> ROne) by (unfold RPool, ROne, NFIX; lia).
    set (b := nth (RPool u) (st_bns s) (bn_nil 0)).
    assert (Hb : bg_ok b) by (apply (Hok (RPool u) Hr Hn)).
    assert (Ebns : st_bns sfin = list_set (st_bns s) (RPool u) (bn_zero_pure b)) by reflexivity.
    assert (Ectx : st_ctx sfin = mkGx (gx_items c) (if (u =? 0)%nat then Some 0%nat
                       else if (u mod BN_CTX_POOL_SIZE =? 0)%nat
                            then match gx_current c with Some k => Some (S k) | None => None end
                            else gx_current c) (S u) (gx_indexes c) (gx_frames c)
                                      (gx_ssize c) (S u) 0 false) by reflexivity.
    assert (Escal : scal_same s sfin) by (unfold scal_same; repeat split; reflexivity).
    clearbody sfin.
    split; [|split].
    + unfold st_wf. rewrite Ebns, Ectx. cbn [gx_items]. rewrite list_set_length. split; [exact E|]. split; [|split].
      * intros r Hr' Hn'. unfold getbn. rewrite Ebns. destruct (Nat.eq_dec (RPool u) r) as [<-|Hne].
        -- rewrite nth_list_set_same by exact Hr. apply bg_ok_zero. exact Hb.
        -- rewrite nth_list_set_other by exact Hne. apply Hok; assumption.
      * unfold getbn. rewrite Ebns. rewrite nth_list_set_other by exact Hn. exact Hone.
      * unfold ctx_wf. cbn [gx_err_stack gx_too_many gx_pused gx_used gx_items gx_current gx_frames gx_ssize gx_indexes].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact W5|].
        split; [|split].
        -- cbn [Nat.eqb]. replace (S u - 1)%nat with u by lia. rewrite W6. fold u. unfold BN_CTX_POOL_SIZE. apply pool_cur_next.
        -- eapply nondecr_set_last; [exact W7|lia].
        -- exact W8.
    + split; [|split; assumption]. unfold blocks_of. rewrite Ebns, Ectx. cbn [gx_items gx_indexes].
      rewrite map_list_set. replace (bn_blocks (bn_zero_pure b)) with (bn_blocks (nth (RPool u) (st_bns s) (bn_nil 0))) by reflexivity.
      rewrite <- (map_nth bn_blocks), list_set_nth_id. exact HP.
    + rewrite Ectx. cbn [gx_used gx_frames]. unfold getbn. rewrite Ebns.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Escal|].
      split; [rewrite list_set_length; lia|]. split; [|split].
      * intros r Hr'. apply nth_list_set_other. congruence.
      * rewrite nth_list_set_same by exact Hr. reflexivity.
      * rewrite nth_list_set_same by exact Hr. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pool_release_spec : forall num pused : nat, (num <= pused)%nat -> (1 <= pused)%nat ->
  pool_release num ((pused - 1) mod 16) (Some ((pused - 1) / 16)%nat) =
  (if (pused - num =? 0)%nat then None else Some ((pused - num - 1) / 16)%nat).
Proof.
  induction num as [|n IH]; intros pused Hn Hp; cbn [pool_release].
  - rewrite Nat.sub_0_r. destruct (Nat.eqb_spec pused 0); [lia|reflexivity].
  - pose proof (Nat.div_mod_eq (pused - 1) 16) as D1. pose proof (Nat.mod_upper_bound (pused - 1) 16 ltac:(lia)) as D2.
    destruct (Nat.eqb_spec ((pused - 1) mod 16) 0) as [Em|Em].
    + destruct (Nat.eq_dec pused 1) as [->|Hne].
      * assert (n = 0)%nat as -> by lia. cbn. reflexivity.
      * assert (Hq : (1 <= (pused - 1) / 16)%nat) by lia.
        destruct ((pused - 1) / 16)%nat as [|q] eqn:Eq; [lia|]. cbn [item_prev].
        specialize (IH (pused - 1)%nat ltac:(lia) ltac:(lia)).
        pose proof (Nat.div_mod_eq (pused - 1 - 1) 16) as D3. pose proof (Nat.mod_upper_bound (pused - 1 - 1) 16 ltac:(lia)) as D4.
        assert (E1 : ((pused - 1 - 1) mod 16 = 15)%nat) by lia.
        assert (E2 : ((pused - 1 - 1) / 16 = q)%nat) by lia.
        rewrite E1, E2 in IH. rewrite IH. replace (pused - 1 - n)%nat with (pused - S n)%nat by lia. reflexivity.
    + specialize (IH (pused - 1)%nat ltac:(lia) ltac:(lia)).
      pose proof (Nat.div_mod_eq (pused - 1 - 1) 16) as D3. pose proof (Nat.mod_upper_bound (pused - 1 - 1) 16 ltac:(lia)) as D4.
      assert (E1 : ((pused - 1 - 1) mod 16 = (pused - 1) mod 16 - 1)%nat) by lia.
      assert (E2 : ((pused - 1 - 1) / 16 = (pused - 1) / 16)%nat) by lia.
      rewrite E1, E2 in IH. rewrite IH. replace (pused - 1 - n)%nat with (pused - S n)%nat by lia. reflexivity.
Qed.

Lemma BN_CTX_end_spec : forall F s fr fp,
  gx_frames (st_ctx s) = fr ++ [fp] ->
  hoare F s (BN_CTX_end ops) (fun _ s' =>
     st_bns s' = st_bns s /\ scal_same s s' /\ gx_used (st_ctx s') = fp /\ gx_frames (st_ctx s') = fr).
Proof.
  intros F s fr fp Efr. apply hoare_wf. intros Hs. pose proof Hs as (E & Hok & Hone & Hcw).
  destruct Hcw as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8).
  unfold BN_CTX_end. apply hoare_bind_getctx. set (c := st_ctx s) in *. set (u := gx_used c) in *.
  rewrite W1. cbn [Nat.eqb negb]. rewrite Efr, rev_app_distr. cbn [rev app]. rewrite rev_involutive.
  rewrite Efr in W7. rewrite <- app_assoc in W7. cbn [app] in W7.
  pose proof (nondecr_last_two _ _ _ W7) as Hfp.
  replace (bsetctx ops _) with (bbind ops (bsetctx ops (mkGx (gx_items c)
             (if (fp <? u)%nat then pool_release (u - fp) ((gx_pused c - 1) mod BN_CTX_POOL_SIZE) (gx_current c) else gx_current c)
             (if (fp <? u)%nat then (gx_pused c - (u - fp))%nat else gx_pused c)
             (gx_indexes c) fr (gx_ssize c) fp 0 false)) (fun _ => bret ops tt)) by reflexivity.
  apply hoare_bind_setctx.
  - intros _. unfold ctx_wf. cbn [gx_err_stack gx_too_many gx_pused gx_used gx_items gx_current gx_frames gx_ssize gx_indexes].
    split; [reflexivity|]. split; [reflexivity|]. rewrite W3. fold u.
    split; [destruct (Nat.ltb_spec fp u); lia|]. split; [lia|]. split; [exact W5|]. split; [|split].
    + destruct (Nat.ltb_spec fp u) as [Hlt|Hge].
      * rewrite W6. fold u. destruct (Nat.eqb_spec u 0) as [|Hu0]; [lia|].
        unfold BN_CTX_POOL_SIZE. rewrite pool_release_spec by lia.
        replace (u - (u - fp))%nat with fp by lia. reflexivity.
      * assert (fp = u) as -> by lia. exact W6.
    + eapply nondecr_drop_last. exact W7.
    + destruct W8 as [(S1 & S2 & S3)|(S1 & S2 & S3)].
      * rewrite Efr in S2. destruct fr; discriminate.
      * right. split; [exact S1|]. split; [exact S2|]. rewrite Efr, length_app in S3. cbn [length] in S3. lia.
  - reflexivity.
  - reflexivity.
  - apply hoare_ret. cbn [set_ctx st_bns st_ctx gx_used gx_frames]. split; [reflexivity|]. split; [unfold scal_same; repeat split; reflexivity|].
    split; reflexivity.
Qed.

End Specs.
