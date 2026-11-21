(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import
  Prog ZIface InflateState Inftrees InflateFast InflateArms.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition weq (w w' : iw) : Prop :=
  w_s w' = w_s w /\ w_r w' = w_r w
  /\ w_c w' = icset_outbuf (w_c w) (ic_outbuf (w_c w'))
  /\ arr_len (ic_outbuf (w_c w')) = arr_len (ic_outbuf (w_c w))
  /\ (forall i, 0 <= i < ir_put (w_r w) -> arr_get (ic_outbuf (w_c w')) i = arr_get (ic_outbuf (w_c w)) i)
  /\ ic_next_out (w_c w) <= ir_put (w_r w).

Lemma weq_refl : forall w, ic_next_out (w_c w) <= ir_put (w_r w) -> weq w w.
Proof. intros [s c r] H. unfold weq. cbn. destruct c; cbn. repeat split; auto. Qed.


Lemma arr_slice_nat_ext : forall n (a a' : arr) ofs,
  (forall i, ofs <= i < ofs + Z.of_nat n -> arr_get a' i = arr_get a i) ->
  arr_slice_nat a' ofs n = arr_slice_nat a ofs n.
Proof.
  induction n as [|n IH]; intros a a' ofs H; cbn; [reflexivity|].
  rewrite (H ofs) by lia. f_equal. apply IH. intros i Hi. apply H. lia.
Qed.

Lemma arr_slice_ext : forall (a a' : arr) ofs n,
  (forall i, ofs <= i < ofs + n -> arr_get a' i = arr_get a i) ->
  arr_slice a' ofs n = arr_slice a ofs n.
Proof.
  intros a a' ofs n H. unfold arr_slice. apply arr_slice_nat_ext. intros i Hi. apply H. lia.
Qed.

Lemma arr_blit_nat_ext : forall n (dst src src' : arr) dofs sofs,
  (forall i, sofs <= i < sofs + Z.of_nat n -> arr_get src' i = arr_get src i) ->
  arr_blit_nat dst dofs src' sofs n = arr_blit_nat dst dofs src sofs n.
Proof.
  induction n as [|n IH]; intros dst src src' dofs sofs H; cbn -[arr_get arr_set]; [reflexivity|].
  rewrite (H sofs) by lia. apply IH. intros i Hi. apply H. lia.
Qed.

Lemma arr_blit_ext : forall (dst src src' : arr) dofs sofs n,
  (forall i, sofs <= i < sofs + n -> arr_get src' i = arr_get src i) ->
  arr_blit dst dofs src' sofs n = arr_blit dst dofs src sofs n.
Proof.
  intros dst src src' dofs sofs n H. unfold arr_blit. apply arr_blit_nat_ext. intros i Hi. apply H. lia.
Qed.

Lemma bytes_ok_slice_at : forall (src : arr) ofs n,
  0 <= ofs -> (forall i, ofs <= i < ofs + n -> 0 <= arr_get src i < 256) ->
  Forall (fun b => 0 <= b < 256) (arr_slice src ofs n).
Proof.
  intros src ofs n Ho H. apply Forall_forall. intros x Hin.
  apply In_nth with (d := 0) in Hin. destruct Hin as (k & Hk & <-).
  unfold arr_slice in Hk |- *. rewrite arr_slice_nat_length in Hk.
  rewrite arr_slice_nat_nth by exact Hk. apply H. lia.
Qed.

Lemma znth_arr_slice : forall (a : arr) ofs n i, 0 <= ofs -> 0 <= i < n ->
  ZIface.znth 0 (arr_slice a ofs n) i = arr_get a (ofs + i).
Proof. intros a ofs n i Ho Hi. rewrite arr_slice_nth by lia. reflexivity. Qed.

Definition agree_below (p : Z) (a a' : arr) : Prop :=
  arr_len a' = arr_len a /\ forall i, 0 <= i < p -> arr_get a' i = arr_get a i.

Lemma agree_below_le : forall p q a a', agree_below p a a' -> q <= p -> agree_below q a a'.
Proof. intros p q a a' [L H] Hq. split; [exact L|]. intros i Hi. apply H. lia. Qed.

Lemma agree_below_set : forall p a a' i v,
  agree_below p a a' -> 0 <= i < arr_len a -> i <= p ->
  agree_below (i + 1) (arr_set a i v) (arr_set a' i v).
Proof.
  intros p a a' i v [L H] Hi Hip. split; [rewrite !arr_len_set; exact L|].
  intros j Hj. rewrite !arr_get_set. unfold arr_inb. rewrite L.
  destruct (Z.eqb_spec i j); cbn [andb].
  - subst j. replace ((0 <=? i) && (i <? arr_len a)) with true; [reflexivity|].
    symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  - apply H. lia.
Qed.

Lemma agree_below_set_same_p : forall p a a' i v,
  agree_below p a a' -> agree_below p (arr_set a i v) (arr_set a' i v).
Proof.
  intros p a a' i v [L H]. split; [rewrite !arr_len_set; exact L|].
  intros j Hj. rewrite !arr_get_set. unfold arr_inb. rewrite L.
  destruct ((i =? j) && _); [reflexivity | apply H; exact Hj].
Qed.

Lemma agree_below_blit_nat : forall n p (a a' src : arr) dofs sofs,
  agree_below p a a' -> 0 <= dofs -> dofs <= p -> dofs + Z.of_nat n <= arr_len a ->
  agree_below (Z.max p (dofs + Z.of_nat n)) (arr_blit_nat a dofs src sofs n) (arr_blit_nat a' dofs src sofs n).
Proof.
  induction n as [|n IH]; intros p a a' src dofs sofs AG Hd Hdp Hn.
  - cbn [arr_blit_nat]. replace (Z.max p (dofs + Z.of_nat 0%nat)) with p by lia. exact AG.
  - cbn -[arr_get arr_set Z.of_nat Z.max]. 
    assert (AG1 : agree_below (Z.max p (dofs + 1)) (arr_set a dofs (arr_get src sofs)) (arr_set a' dofs (arr_get src sofs))).
    { destruct (Z.le_gt_cases p dofs).
      - replace (Z.max p (dofs + 1)) with (dofs + 1) by lia. apply (agree_below_set p); [exact AG | lia | lia].
      - replace (Z.max p (dofs + 1)) with p by lia. apply agree_below_set_same_p. exact AG. }
    pose proof (IH (Z.max p (dofs + 1)) _ _ src (dofs + 1) (sofs + 1) AG1 ltac:(lia) ltac:(lia) ltac:(rewrite arr_len_set; lia)) as IH'.
    replace (Z.max (Z.max p (dofs + 1)) (dofs + 1 + Z.of_nat n)) with (Z.max p (dofs + Z.of_nat (S n))) in IH' by lia.
    exact IH'.
Qed.

Lemma agree_below_blit : forall p (a a' src : arr) dofs sofs n,
  agree_below p a a' -> 0 <= dofs -> dofs <= p -> 0 <= n -> dofs + n <= arr_len a ->
  agree_below (Z.max p (dofs + n)) (arr_blit a dofs src sofs n) (arr_blit a' dofs src sofs n).
Proof.
  intros p a a' src dofs sofs n AG Hd Hdp Hn Hlen. unfold arr_blit.
  rewrite <- (Z2Nat.id n) at 1 by lia. apply agree_below_blit_nat; try assumption; rewrite Z2Nat.id; lia.
Qed.

Lemma ic_outbuf_set : forall c ob, ic_outbuf (icset_outbuf c ob) = ob.
Proof. intros [] ob; reflexivity. Qed.
Lemma icset_outbuf_twice : forall c a b, icset_outbuf (icset_outbuf c a) b = icset_outbuf c b.
Proof. intros [] a b; reflexivity. Qed.
Lemma icset_outbuf_self : forall c, icset_outbuf c (ic_outbuf c) = c.
Proof. intros []; reflexivity. Qed.
Lemma ic_input_set : forall c ob, ic_input (icset_outbuf c ob) = ic_input c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_next_in_set : forall c ob, ic_next_in (icset_outbuf c ob) = ic_next_in c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_avail_in_set : forall c ob, ic_avail_in (icset_outbuf c ob) = ic_avail_in c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_next_out_set : forall c ob, ic_next_out (icset_outbuf c ob) = ic_next_out c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_avail_out_set : forall c ob, ic_avail_out (icset_outbuf c ob) = ic_avail_out c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_total_in_set : forall c ob, ic_total_in (icset_outbuf c ob) = ic_total_in c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_total_out_set : forall c ob, ic_total_out (icset_outbuf c ob) = ic_total_out c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_adler_set : forall c ob, ic_adler (icset_outbuf c ob) = ic_adler c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_data_type_set : forall c ob, ic_data_type (icset_outbuf c ob) = ic_data_type c.
Proof. intros [] ob; reflexivity. Qed.
Lemma ic_msg_set : forall c ob, ic_msg (icset_outbuf c ob) = ic_msg c.
Proof. intros [] ob; reflexivity. Qed.
Create HintDb icr discriminated.
#[export] Hint Rewrite ic_outbuf_set icset_outbuf_twice icset_outbuf_self ic_input_set ic_next_in_set ic_avail_in_set
  ic_next_out_set ic_avail_out_set ic_total_in_set ic_total_out_set ic_adler_set ic_data_type_set ic_msg_set : icr.


Lemma land_ones_bound : forall a n, 0 <= n -> 0 <= Z.land a (Z.ones n) < 2 ^ n.
Proof. intros a n Hn. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. Qed.

Lemma zmask_ones : forall n, 0 <= n -> zmask n = Z.ones (Z.min n 32).
Proof.
  intros n Hn. unfold zmask, wrap32. rewrite Z.shiftl_1_l. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia.
  unfold Z.ones. rewrite !Z.shiftl_1_l.
  destruct (Z.le_gt_cases n 32).
  - rewrite Z.min_l by lia. rewrite Z.mod_small; [lia|]. split; [pose proof (Z.pow_pos_nonneg 2 n); lia|].
    pose proof (Z.pow_le_mono_r 2 n 32). lia.
  - rewrite Z.min_r by lia.
    replace n with ((n - 32) + 32) at 1 by lia. rewrite Z.pow_add_r by lia.
    rewrite <- Zminus_mod_idemp_l. rewrite Z.mod_mul by lia. reflexivity.
Qed.

Lemma BITSv_bound : forall hold n, 0 <= n -> 0 <= BITSv hold n < 2 ^ n.
Proof.
  intros hold n Hn. unfold BITSv. rewrite zmask_ones by lia.
  pose proof (land_ones_bound (wrap32 hold) (Z.min n 32) ltac:(lia)) as H.
  pose proof (Z.pow_le_mono_r 2 (Z.min n 32) n ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma code_op_bound : forall e, 0 <= code_op e < 256.
Proof. intros e. unfold code_op. change 255 with (Z.ones 8). apply land_ones_bound. lia. Qed.
Lemma code_bits_bound : forall e, 0 <= code_bits e < 256.
Proof. intros e. unfold code_bits. change 255 with (Z.ones 8). apply land_ones_bound. lia. Qed.
Lemma code_val_bound : forall e, 0 <= code_val e < 65536.
Proof. intros e. unfold code_val. change 65535 with (Z.ones 16). apply land_ones_bound. lia. Qed.
Lemma link_op_lt16 : forall e, Z.land (code_op e) 240 = 0 -> code_op e < 16.
Proof.
  intros e H. pose proof (code_op_bound e) as [H0 H1].
  assert (E : code_op e = Z.land (code_op e) 255).
  { unfold code_op. rewrite <- Z.land_assoc. reflexivity. }
  rewrite E. replace 255 with (Z.lor 240 15) by reflexivity. rewrite Z.land_lor_distr_r, H, Z.lor_0_l.
  change 15 with (Z.ones 4). pose proof (land_ones_bound (code_op e) 4 ltac:(lia)) as H2. cbn in H2. lia.
Qed.

Definition zupto (n : Z) : list Z := map Z.of_nat (seq 0 (Z.to_nat n)).
Lemma zupto_spec : forall n i, In i (zupto n) <-> 0 <= i < n.
Proof.
  intros n i. unfold zupto. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hi. exists (Z.to_nat i). split; [lia|]. apply in_seq. lia.
Qed.
Lemma forallb_zupto : forall f n, forallb f (zupto n) = true -> forall i, 0 <= i < n -> f i = true.
Proof. intros f n H i Hi. rewrite forallb_forall in H. apply H. apply zupto_spec. exact Hi. Qed.


Definition ares_rel {A} (a a' : ares A) : Prop :=
  match a, a' with
  | ARun x w1, ARun x' w1' => x' = x /\ weq w1 w1'
  | ALeave w1, ALeave w1' => weq w1 w1'
  | ARet rc w1, ARet rc' w1' => rc' = rc /\ weq w1 w1'
  | _, _ => False
  end.

Definition WP {A} (chk : iw -> bool) (m : AM A) : Prop :=
  forall w w', chk w' = true -> weq w w' -> ares_rel (m w) (m w').
Definition ctrue : iw -> bool := fun _ => true.
Definition WP0 {A} (m : AM A) : Prop := WP ctrue m.

Definition after {A} (m : AM A) (chk : A -> iw -> bool) (w : iw) : bool :=
  match m w with ARun a w1 => chk a w1 | _ => true end.

Lemma WP_mono : forall {A} (chk chk' : iw -> bool) (m : AM A),
  (forall w, chk' w = true -> chk w = true) -> WP chk m -> WP chk' m.
Proof. intros A chk chk' m H HW w w' C E. apply HW; [apply H; exact C | exact E]. Qed.

Lemma WP0_WP : forall {A} chk (m : AM A), WP0 m -> WP chk m.
Proof. intros A chk m H. apply (WP_mono ctrue); [reflexivity | exact H]. Qed.

Lemma WP_bind : forall {A B} chk1 (m : AM A) chk2 (f : A -> AM B),
  WP chk1 m -> (forall a, WP (chk2 a) (f a)) ->
  WP (fun w => chk1 w && after m chk2 w) (abind m f).
Proof.
  intros A B chk1 m chk2 f H1 H2 w w' C E. apply andb_prop in C as [C1 C2]. unfold after in C2.
  unfold abind. specialize (H1 w w' C1 E). destruct (m w) as [a w1|w1|rc w1]; destruct (m w') as [a' w1'|w1'|rc' w1']; cbn in H1; try contradiction.
  - destruct H1 as [-> E1]. apply H2; [exact C2 | exact E1].
  - exact H1.
  - exact H1.
Qed.

Lemma WP_bind0l : forall {A B} (m : AM A) chk2 (f : A -> AM B),
  WP0 m -> (forall a, WP (chk2 a) (f a)) -> WP (after m chk2) (abind m f).
Proof.
  intros A B m chk2 f H1 H2. apply (WP_mono (fun w => ctrue w && after m chk2 w)); [|apply WP_bind; assumption].
  intros w C. exact C.
Qed.

Lemma WP_bind0 : forall {A B} (m : AM A) (f : A -> AM B),
  WP0 m -> (forall a, WP0 (f a)) -> WP0 (abind m f).
Proof.
  intros A B m f H1 H2. unfold WP0. apply (WP_mono (fun w => ctrue w && after m (fun _ => ctrue) w)); [|apply WP_bind; assumption].
  intros w _. unfold after, ctrue. destruct (m w); reflexivity.
Qed.

Lemma WP_bind0r : forall {A B} chk (m : AM A) (f : A -> AM B),
  WP chk m -> (forall a, WP0 (f a)) -> WP chk (abind m f).
Proof.
  intros A B chk m f H1 H2. apply (WP_mono (fun w => chk w && after m (fun _ => ctrue) w)); [|apply WP_bind; assumption].
  intros w C. rewrite C. unfold after, ctrue. destruct (m w); reflexivity.
Qed.

Lemma WP_aret : forall {A} (a : A), WP0 (aret a).
Proof. intros A a w w' _ E. cbn. auto. Qed.
Lemma WP_aleave : forall {A}, WP0 (@aleave A).
Proof. intros A w w' _ E. exact E. Qed.
Lemma WP_areturn : forall {A} rc, WP0 (@areturn A rc).
Proof. intros A rc w w' _ E. cbn. auto. Qed.

Lemma WP_gs : forall {A} (f : inflate_state -> A), WP0 (gs f).
Proof. intros A f w w' _ E. cbn. rewrite (proj1 E). split; [reflexivity | exact E]. Qed.
Lemma WP_gr : forall {A} (f : iregs -> A), WP0 (gr f).
Proof. intros A f w w' _ E. cbn. rewrite (proj1 (proj2 E)). split; [reflexivity | exact E]. Qed.
Lemma WP_gc : forall {A} (f : icall -> A),
  (forall c ob, f (icset_outbuf c ob) = f c) -> WP0 (gc f).
Proof. intros A f Hf w w' _ E. cbn. rewrite (proj1 (proj2 (proj2 E))), Hf. split; [reflexivity | exact E]. Qed.

Lemma WP_us : forall (f : inflate_state -> inflate_state), WP0 (us f).
Proof.
  intros f w w' _ (Hs & Hr & Hc & L & AG & NO). cbn. split; [reflexivity|].
  unfold weq; cbn. rewrite Hs, Hr. repeat split; assumption.
Qed.
Lemma WP_ur : forall (f : iregs -> iregs),
  (forall r, ir_put (f r) = ir_put r) -> WP0 (ur f).
Proof.
  intros f Hf w w' _ (Hs & Hr & Hc & L & AG & NO). cbn. split; [reflexivity|].
  unfold weq; cbn. rewrite Hs, Hr, Hf. repeat split; assumption.
Qed.
Lemma WP_uc : forall (f : icall -> icall),
  (forall c ob, f (icset_outbuf c ob) = icset_outbuf (f c) ob) ->
  (forall c, ic_outbuf (f c) = ic_outbuf c) ->
  (forall c, ic_next_out (f c) = ic_next_out c) ->
  WP0 (uc f).
Proof.
  intros f H1 H2 H3 w w' _ (Hs & Hr & Hc & L & AG & NO). cbn. split; [reflexivity|].
  unfold weq; cbn. rewrite Hs, Hr, Hc, H1, !H2, H3. autorewrite with icr. repeat split; assumption.
Qed.

Lemma WP_if : forall {A} (b : bool) chk1 chk2 (m1 m2 : AM A),
  WP chk1 m1 -> WP chk2 m2 -> WP (fun w => if b then chk1 w else chk2 w) (if b then m1 else m2).
Proof. intros A [|] chk1 chk2 m1 m2 H1 H2; assumption. Qed.
Lemma WP_if0 : forall {A} (b : bool) (m1 m2 : AM A),
  WP0 m1 -> WP0 m2 -> WP0 (if b then m1 else m2).
Proof. intros A [|] m1 m2 H1 H2; assumption. Qed.

Lemma WP_bind_inv : forall {A B} chk (m : AM A) (f : A -> AM B),
  WP chk m -> (forall w a w1, chk w = true -> m w = ARun a w1 -> chk w1 = true) ->
  (forall a, WP chk (f a)) -> WP chk (abind m f).
Proof.
  intros A B chk m f H1 HK H2. apply (WP_mono (fun w => chk w && after m (fun _ => chk) w)); [|apply WP_bind; assumption].
  intros w C. rewrite C. unfold after. destruct (m w) as [a w1| |] eqn:E; try reflexivity. cbn. exact (HK w a w1 C E).
Qed.

Definition keeps {A} (chk : iw -> bool) (m : AM A) : Prop :=
  forall w a w1, chk w = true -> m w = ARun a w1 -> chk w1 = true.
Lemma keeps_bind : forall {A B} chk (m : AM A) (f : A -> AM B),
  keeps chk m -> (forall a, keeps chk (f a)) -> keeps chk (abind m f).
Proof.
  intros A B chk m f H1 H2 w b w1 C E. unfold abind in E.
  destruct (m w) as [a w'| |] eqn:Em; try discriminate E. exact (H2 a w' b w1 (H1 w a w' C Em) E).
Qed.
Lemma keeps_if : forall {A} chk (c : bool) (m1 m2 : AM A),
  keeps chk m1 -> keeps chk m2 -> keeps chk (if c then m1 else m2).
Proof. intros A chk [|] m1 m2 H1 H2; assumption. Qed.
Lemma WP_bind_keeps : forall {A B} chk (m : AM A) (f : A -> AM B),
  WP chk m -> keeps chk m -> (forall a, WP chk (f a)) -> WP chk (abind m f).
Proof. intros A B chk m f H1 HK H2. apply WP_bind_inv; assumption. Qed.

Lemma WP_aget : forall {A} (K : iw -> AM A),
  (forall s c r ob, K (mkW s (icset_outbuf c ob) r) = K (mkW s c r)) ->
  (forall w, WP0 (K w)) -> WP0 (abind aget K).
Proof.
  intros A K HK HW w w' C E. cbn [abind aget]. pose proof E as (Hs & Hr & Hc & _).
  destruct w as [s c r], w' as [s' c' r']; cbn in Hs, Hr, Hc. subst s' r'. rewrite Hc at 1. rewrite HK.
  apply HW; [exact C | exact E].
Qed.

Lemma WP_amodify : forall (f : iw -> iw),
  (forall w w', weq w w' -> weq (f w) (f w')) -> WP0 (amodify f).
Proof. intros f Hf w w' _ E. cbn. split; [reflexivity | apply Hf; exact E]. Qed.

Lemma weq_RESTORE : forall w w', weq w w' -> weq (RESTORE w) (RESTORE w').
Proof.
  intros [s c r] [s' c' r'] (Hs & Hr & Hc & L & AG & NO); cbn in *. subst s' r'. rewrite Hc.
  unfold weq, RESTORE; cbn. destruct c; cbn in *. repeat split; try assumption. lia.
Qed.
Lemma weq_LOAD : forall w w', weq w w' -> ic_next_out (w_c w) = ir_put (w_r w) -> weq (LOAD w) (LOAD w').
Proof.
  intros [s c r] [s' c' r'] (Hs & Hr & Hc & L & AG & NO) Hno; cbn in *. subst s' r'. rewrite Hc.
  unfold weq, LOAD; cbn. destruct c; cbn in *. rewrite Hno. repeat split; try assumption. lia.
Qed.


Lemma WP_PULLBYTE : WP0 PULLBYTE.
Proof.
  intros w w' _ (Hs & Hr & Hc & L & AG & NO). unfold PULLBYTE. rewrite Hr, Hc.
  cbn [ic_input icset_outbuf]. replace (ic_input (icset_outbuf (w_c w) (ic_outbuf (w_c w')))) with (ic_input (w_c w)) by (destruct (w_c w); reflexivity).
  destruct (ir_have (w_r w) =? 0).
  - unfold weq. repeat split; assumption.
  - cbn. split; [reflexivity|]. unfold weq; cbn. rewrite Hs, Hc. repeat split; try assumption.
Qed.

Lemma WP_NEEDBITS_k : forall k n, WP0 (NEEDBITS_k k n).
Proof.
  induction k as [|k IH]; intros n; cbn [NEEDBITS_k].
  - apply WP_aret.
  - apply WP_bind0; [apply WP_gr|]. intros bits. apply WP_if0; [|apply WP_aret].
    apply WP_bind0; [apply WP_PULLBYTE | intros _; apply IH].
Qed.
Lemma WP_NEEDBITS : forall n, WP0 (NEEDBITS n).
Proof. intros n. apply WP_NEEDBITS_k. Qed.
Lemma PULLBYTE_frame : forall w a w1, PULLBYTE w = ARun a w1 ->
  w_s w1 = w_s w /\ w_c w1 = w_c w /\ ir_put (w_r w1) = ir_put (w_r w) /\ ir_left (w_r w1) = ir_left (w_r w)
  /\ ir_out (w_r w1) = ir_out (w_r w) /\ ir_in (w_r w1) = ir_in (w_r w) /\ ir_ret (w_r w1) = ir_ret (w_r w).
Proof.
  intros w a w1 E. unfold PULLBYTE in E. destruct (ir_have (w_r w) =? 0); [discriminate E|].
  injection E; intros <- _. destruct w as [s c r]; cbn. repeat split; reflexivity.
Qed.
Lemma NEEDBITS_k_frame : forall k n w a w1, NEEDBITS_k k n w = ARun a w1 ->
  w_s w1 = w_s w /\ w_c w1 = w_c w /\ ir_put (w_r w1) = ir_put (w_r w) /\ ir_left (w_r w1) = ir_left (w_r w)
  /\ ir_out (w_r w1) = ir_out (w_r w) /\ ir_in (w_r w1) = ir_in (w_r w) /\ ir_ret (w_r w1) = ir_ret (w_r w).
Proof.
  induction k as [|k IH]; intros n w a w1 E; cbn [NEEDBITS_k] in E.
  - injection E; intros <- _. repeat split; reflexivity.
  - unfold abind, gr in E. destruct (ir_bits (w_r w) <? n).
    + destruct (PULLBYTE w) as [u w2| |] eqn:E2; try discriminate E.
      destruct (PULLBYTE_frame w u w2 E2) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
      destruct (IH n w2 a w1 E) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
      rewrite B1, B2, B3, B4, B5, B6, B7. repeat split; assumption.
    + injection E; intros <- _. repeat split; reflexivity.
Qed.
Lemma NEEDBITS_frame : forall n w a w1, NEEDBITS n w = ARun a w1 ->
  w_s w1 = w_s w /\ w_c w1 = w_c w /\ ir_put (w_r w1) = ir_put (w_r w) /\ ir_left (w_r w1) = ir_left (w_r w)
  /\ ir_out (w_r w1) = ir_out (w_r w) /\ ir_in (w_r w1) = ir_in (w_r w) /\ ir_ret (w_r w1) = ir_ret (w_r w).
Proof. intros n. apply NEEDBITS_k_frame. Qed.

Lemma PULLBYTE_have : forall w a w1, PULLBYTE w = ARun a w1 -> 0 <= ir_have (w_r w) -> 0 <= ir_have (w_r w1).
Proof.
  intros w a w1 E H. unfold PULLBYTE in E. destruct (ir_have (w_r w) =? 0); [discriminate E|].
  injection E; intros <- _. cbn. apply wrap32_range.
Qed.
Lemma NEEDBITS_k_have : forall k n w a w1, NEEDBITS_k k n w = ARun a w1 -> 0 <= ir_have (w_r w) -> 0 <= ir_have (w_r w1).
Proof.
  induction k as [|k IH]; intros n w a w1 E H; cbn [NEEDBITS_k] in E.
  - injection E; intros <- _. exact H.
  - unfold abind, gr in E. destruct (ir_bits (w_r w) <? n).
    + destruct (PULLBYTE w) as [u w2| |] eqn:E2; try discriminate E.
      apply (IH n w2 a w1 E). apply (PULLBYTE_have w u w2 E2 H).
    + injection E; intros <- _. exact H.
Qed.
Lemma NEEDBITS_have : forall n w a w1, NEEDBITS n w = ARun a w1 -> 0 <= ir_have (w_r w) -> 0 <= ir_have (w_r w1).
Proof. intros n. apply NEEDBITS_k_have. Qed.

Lemma WP_gs_bind : forall {B} (chk2 : inflate_state -> iw -> bool) (K : inflate_state -> AM B),
  (forall s, WP (chk2 s) (K s)) -> WP (fun w => chk2 (w_s w) w) (abind (gs (fun s => s)) K).
Proof. intros B chk2 K H. apply (WP_mono (after (gs (fun s => s)) chk2)); [intros w C; exact C|]. apply WP_bind0l; [apply WP_gs | exact H]. Qed.
Lemma WP_gr_bind : forall {B} (chk2 : iregs -> iw -> bool) (K : iregs -> AM B),
  (forall r, WP (chk2 r) (K r)) -> WP (fun w => chk2 (w_r w) w) (abind (gr (fun r => r)) K).
Proof. intros B chk2 K H. apply (WP_mono (after (gr (fun r => r)) chk2)); [intros w C; exact C|]. apply WP_bind0l; [apply WP_gr | exact H]. Qed.

Lemma WP_BITS : forall n, WP0 (BITS n).
Proof. intros n. apply WP_gr. Qed.
Lemma WP_HOLD : WP0 HOLD.
Proof. apply WP_gr. Qed.
Lemma WP_DROPBITS : forall n, WP0 (DROPBITS n).
Proof. intros n. apply WP_ur. reflexivity. Qed.
Lemma WP_INITBITS : WP0 INITBITS.
Proof. apply WP_ur. reflexivity. Qed.
Lemma WP_BYTEBITS : WP0 BYTEBITS.
Proof. apply WP_ur. reflexivity. Qed.
Lemma WP_set_mode : forall m, WP0 (set_mode m).
Proof. intros m. apply WP_us. Qed.
Lemma WP_set_msg : forall m, WP0 (set_msg m).
Proof. intros m. apply WP_uc; intros; try destruct c; reflexivity. Qed.
Lemma WP_go_bad : forall m, WP0 (go_bad m).
Proof. intros m. apply WP_bind0; [apply WP_set_msg | intros _; apply WP_set_mode]. Qed.
Lemma WP_set_adler_check : forall v, WP0 (set_adler_check v).
Proof. intros v. apply WP_bind0; [apply WP_us | intros _; apply WP_uc; intros; try destruct c; reflexivity]. Qed.

Lemma WP_DECODE_k : forall k p index need, WP0 (DECODE_k k p index need).
Proof.
  induction k as [|k IH]; intros p index need; cbn [DECODE_k].
  - apply WP_bind0; [apply WP_HOLD | intros hold; apply WP_gs].
  - apply WP_bind0; [apply WP_HOLD | intros hold].
    apply WP_bind0; [apply WP_gr | intros bits].
    apply WP_bind0; [apply WP_gs | intros here].
    apply WP_if0; [apply WP_aret|]. apply WP_bind0; [apply WP_PULLBYTE | intros _; apply IH].
Qed.
Lemma WP_DECODE1 : forall p nbits, WP0 (DECODE1 p nbits).
Proof. intros. apply WP_DECODE_k. Qed.
Lemma WP_DECODE2 : forall p last, WP0 (DECODE2 p last).
Proof. intros. apply WP_DECODE_k. Qed.

Lemma DECODE_k_res : forall k p index need w here w1, DECODE_k k p index need w = ARun here w1 ->
  here = code_at (w_s w) p (index (ir_hold (w_r w1)))
  /\ w_s w1 = w_s w /\ w_c w1 = w_c w /\ ir_put (w_r w1) = ir_put (w_r w) /\ ir_left (w_r w1) = ir_left (w_r w)
  /\ ir_out (w_r w1) = ir_out (w_r w) /\ ir_ret (w_r w1) = ir_ret (w_r w).
Proof.
  induction k as [|k IH]; intros p index need w here w1 E; cbn [DECODE_k] in E; unfold abind, HOLD, gr, gs in E.
  - injection E; intros <- <-. repeat split; reflexivity.
  - destruct (need _ <=? _).
    + injection E; intros <- <-. repeat split; reflexivity.
    + destruct (PULLBYTE w) as [u w2| |] eqn:E2; try discriminate E.
      destruct (PULLBYTE_frame w u w2 E2) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
      destruct (IH p index need w2 here w1 E) as (B0 & B1 & B2 & B3 & B4 & B5 & B7).
      rewrite B0, B1, B2, B3, B4, B5, B7, A1. repeat split; assumption.
Qed.

Definition frame_chk (chk : iw -> bool) : Prop :=
  forall w w1, w_s w1 = w_s w -> w_c w1 = w_c w -> ir_put (w_r w1) = ir_put (w_r w) ->
    ir_left (w_r w1) = ir_left (w_r w) -> ir_out (w_r w1) = ir_out (w_r w) -> chk w1 = chk w.
Lemma keeps_NEEDBITS : forall chk n, frame_chk chk -> keeps chk (NEEDBITS n).
Proof.
  intros chk n H w a w1 C E. destruct (NEEDBITS_frame _ _ _ _ E) as (F1 & F2 & F3 & F4 & F5 & _).
  rewrite (H w w1 F1 F2 F3 F4 F5). exact C.
Qed.
Lemma keeps_DECODE_k : forall chk k p index need, frame_chk chk -> keeps chk (DECODE_k k p index need).
Proof.
  intros chk k p index need H w a w1 C E. destruct (DECODE_k_res _ _ _ _ _ _ _ E) as (_ & F1 & F2 & F3 & F4 & F5 & _).
  rewrite (H w w1 F1 F2 F3 F4 F5). exact C.
Qed.

Lemma WP_crc_input : forall copy, WP0 (crc_input copy).
Proof.
  intros copy w w' _ (Hs & Hr & Hc & L & AG & NO). unfold crc_input. rewrite Hs, Hr, Hc.
  replace (ic_input (icset_outbuf (w_c w) (ic_outbuf (w_c w')))) with (ic_input (w_c w)) by (destruct (w_c w); reflexivity).
  cbn. split; [reflexivity|]. unfold weq; cbn. rewrite Hr, Hc. repeat split; assumption.
Qed.
Lemma WP_CRC2 : forall word, WP0 (CRC2 word).
Proof. intros. apply WP_us. Qed.
Lemma WP_CRC4 : forall word, WP0 (CRC4 word).
Proof. intros. apply WP_us. Qed.

Lemma WP_set_lens : forall i v, WP0 (set_lens i v).
Proof. intros. apply WP_us. Qed.
Lemma WP_lens_repeat : forall copy len, WP0 (lens_repeat copy len).
Proof. intros. apply WP_us. Qed.

Lemma WP_name_like : forall flag, WP0 (name_like flag).
Proof.
  intros flag. unfold name_like.
  apply WP_bind0; [apply WP_gs | intros s]. apply WP_if0; [|apply WP_aret].
  apply WP_bind0; [apply WP_gr | intros r]. apply WP_if0; [apply WP_aret|].
  apply WP_aget.
  - intros s0 c r0 ob. cbn [w_c]. rewrite ic_input_set. reflexivity.
  - intros w0. destruct (scan_zero _ _ _) as [copy len].
    apply WP_bind0; [apply WP_if0; [apply WP_crc_input | apply WP_aret] | intros _].
    apply WP_bind0; [apply WP_ur; reflexivity | intros _]. apply WP_if0; apply WP_aret.
Qed.

Ltac wp0_step :=
  lazymatch goal with
  | |- WP0 (abind aget _) => apply WP_aget; [intros; cbn [w_c w_s w_r]; autorewrite with icr; reflexivity | intros]
  | |- WP0 (abind _ _) => apply WP_bind0; [|intros]
  | |- WP0 (if _ then _ else _) => apply WP_if0
  | |- WP0 (aret _) => apply WP_aret
  | |- WP0 aleave => apply WP_aleave
  | |- WP0 (areturn _) => apply WP_areturn
  | |- WP0 (gs _) => apply WP_gs
  | |- WP0 (gr _) => apply WP_gr
  | |- WP0 (gc _) => apply WP_gc; intros [] ?; reflexivity
  | |- WP0 (us _) => apply WP_us
  | |- WP0 (ur _) => apply WP_ur; intros []; reflexivity
  | |- WP0 (uc _) => apply WP_uc; [intros [] ? | intros [] | intros []]; reflexivity
  | |- WP0 (amodify RESTORE) => apply WP_amodify; apply weq_RESTORE
  | |- WP0 PULLBYTE => apply WP_PULLBYTE
  | |- WP0 (NEEDBITS_k _ _) => apply WP_NEEDBITS_k
  | |- WP0 (NEEDBITS _) => apply WP_NEEDBITS
  | |- WP0 (BITS _) => apply WP_BITS
  | |- WP0 HOLD => apply WP_HOLD
  | |- WP0 (DROPBITS _) => apply WP_DROPBITS
  | |- WP0 INITBITS => apply WP_INITBITS
  | |- WP0 BYTEBITS => apply WP_BYTEBITS
  | |- WP0 (set_mode _) => apply WP_set_mode
  | |- WP0 (set_msg _) => apply WP_set_msg
  | |- WP0 (go_bad _) => apply WP_go_bad
  | |- WP0 (set_adler_check _) => apply WP_set_adler_check
  | |- WP0 (DECODE_k _ _ _ _) => apply WP_DECODE_k
  | |- WP0 (DECODE1 _ _) => apply WP_DECODE1
  | |- WP0 (DECODE2 _ _) => apply WP_DECODE2
  | |- WP0 (crc_input _) => apply WP_crc_input
  | |- WP0 (CRC2 _) => apply WP_CRC2
  | |- WP0 (CRC4 _) => apply WP_CRC4
  | |- WP0 (set_lens _ _) => apply WP_set_lens
  | |- WP0 (lens_repeat _ _) => apply WP_lens_repeat
  | |- WP0 (name_like _) => apply WP_name_like
  | |- WP0 (aux _ _) => unfold aux; apply WP_if0; [apply WP_us | apply WP_aret]
  | |- WP0 (set_back _ _) => unfold set_back, aux; apply WP_if0; [apply WP_us | apply WP_aret]
  | |- WP0 (add_back _ _) => unfold add_back, aux; apply WP_if0; [apply WP_us | apply WP_aret]
  | |- WP0 (match ?x with _ => _ end) => destruct x
  | |- WP0 (let x := _ in _) => cbv zeta
  end.
Ltac wp0 := repeat wp0_step.

Lemma weq_canon : forall w w', weq w w' ->
  exists ob', w' = mkW (w_s w) (icset_outbuf (w_c w) ob') (w_r w)
    /\ agree_below (ir_put (w_r w)) (ic_outbuf (w_c w)) ob' /\ ic_next_out (w_c w) <= ir_put (w_r w).
Proof.
  intros [s c r] [s' c' r'] (Hs & Hr & Hc & L & AG & NO); cbn in *. subst s' r'.
  exists (ic_outbuf c'). rewrite <- Hc. split; [reflexivity|]. split; [split; assumption | exact NO].
Qed.
Lemma weq_mk : forall s c r ob', agree_below (ir_put r) (ic_outbuf c) ob' -> ic_next_out c <= ir_put r ->
  weq (mkW s c r) (mkW s (icset_outbuf c ob') r).
Proof.
  intros s c r ob' [L AG] NO. unfold weq; cbn. autorewrite with icr. repeat split; assumption.
Qed.
Lemma weq_mk' : forall s c c' r, c' = icset_outbuf c (ic_outbuf c') ->
  agree_below (ir_put r) (ic_outbuf c) (ic_outbuf c') -> ic_next_out c <= ir_put r ->
  weq (mkW s c r) (mkW s c' r).
Proof. intros s c c' r E AG NO. rewrite E in AG |- *. rewrite ic_outbuf_set in AG. apply weq_mk; [exact AG | exact NO]. Qed.

Ltac am_cbn :=
  cbn beta iota zeta delta [abind aret gs gc gr us ur uc aleave areturn amodify agets aget aput w_s w_c w_r wset_s wset_r wset_c
       BITS HOLD DROPBITS INITBITS BYTEBITS set_mode set_msg go_bad set_adler_check
       is_mode is_last is_wrap is_havedict is_flags is_dmax is_check is_total is_head is_wbits is_wsize is_whave is_wnext
       is_window is_window_blk is_hold is_bits is_length is_offset is_extra is_lencode is_distcode is_lenbits is_distbits
       is_ncode is_nlen is_ndist is_have is_next is_lens is_work is_codes is_sane is_back is_was is_self_blk
       iset_mode iset_last iset_wrap iset_havedict iset_flags iset_dmax iset_check iset_total iset_head iset_wbits iset_wsize
       iset_whave iset_wnext iset_window iset_window_blk iset_hold iset_bits iset_length iset_offset iset_extra iset_lencode
       iset_distcode iset_lenbits iset_distbits iset_ncode iset_nlen iset_ndist iset_have iset_next iset_lens iset_work
       iset_codes iset_sane iset_back iset_was iset_self_blk
       ic_input ic_next_in ic_avail_in ic_outbuf ic_next_out ic_avail_out ic_total_in ic_total_out ic_adler ic_data_type ic_msg
       icset_next_in icset_avail_in icset_outbuf icset_next_out icset_avail_out icset_total_in icset_total_out icset_adler
       icset_data_type icset_msg
       ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret
       irset_next irset_have irset_put irset_left irset_hold irset_bits irset_in irset_out irset_ret
       fst snd].

Ltac wp_canon :=
  let w := fresh "w" in let w' := fresh "w'" in let C := fresh "C" in let E := fresh "E" in
  let ob' := fresh "ob'" in
  intros w w' C E;
  let H := fresh in
  destruct (weq_canon w w' E) as (ob' & H & AG & NO); rewrite H in C |- *; clear H E;
  destruct w as [s c r]; cbn [w_s w_c w_r] in C, AG, NO |- *.

Ltac am_red :=
  lazy beta iota zeta delta [abind aret gs gc gr us ur uc aleave areturn amodify agets aget aput wset_s wset_r wset_c
                             set_mode set_msg go_bad set_adler_check BITS HOLD DROPBITS INITBITS BYTEBITS].
Ltac am_red_in H :=
  lazy beta iota zeta delta [abind aret gs gc gr us ur uc aleave areturn amodify agets aget aput wset_s wset_r wset_c
                             set_mode set_msg go_bad set_adler_check BITS HOLD DROPBITS INITBITS BYTEBITS] in H.

Lemma WP_aux : forall iv f, WP0 (aux iv f).
Proof. intros iv f. unfold aux. destruct (iv_aux iv); [apply WP_us | apply WP_aret]. Qed.
Lemma WP_set_back : forall iv v, WP0 (set_back iv v).
Proof. intros. apply WP_aux. Qed.
Lemma WP_add_back : forall iv v, WP0 (add_back iv v).
Proof. intros. apply WP_aux. Qed.
