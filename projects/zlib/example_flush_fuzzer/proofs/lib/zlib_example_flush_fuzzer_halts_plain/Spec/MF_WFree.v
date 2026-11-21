(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree MI_WFree2 MI_WKill MI_WNtf MI_WNtf2 MI_Sim MI_WTry2 MI_WSlot LB_WNtf MF_Defs MF_Inv.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Definition cb (st : mstate) : gmap Z Z := c_bounces (s_ctx st).

Lemma cb_bounces st st' i : cb st' = cb st -> bounces st' i = bounces st i.
Proof. unfold cb, bounces, ctx. intros E. rewrite E. reflexivity. Qed.

Lemma cb_upd_meta m f st : cb (upd_meta m f st) = cb st. Proof. reflexivity. Qed.
Lemma cb_put_meta m r st : cb (put_meta m r st) = cb st. Proof. reflexivity. Qed.
Lemma cb_set_head h v st : cb (set_head h v st) = cb st. Proof. destruct h; reflexivity. Qed.
Lemma cb_set_usage sc v st : cb (set_usage sc v st) = cb st. Proof. reflexivity. Qed.
Lemma cb_del_group g st : cb (del_group g st) = cb st. Proof. reflexivity. Qed.
Lemma cb_del_slots p s n st : cb (del_slots p s n st) = cb st. Proof. reflexivity. Qed.
Lemma cb_record_seq sc st : cb (record_seq sc st) = cb st. Proof. unfold record_seq. destruct (sc_in_seq_range sc); reflexivity. Qed.
Lemma cb_step_seq st : cb (step_seq st) = cb st. Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); reflexivity. Qed.
Lemma cb_dequeue h m st : cb (dequeue h m st) = cb st.
Proof.
  unfold dequeue. destruct (negb (optr_eqb (m_next (get_meta_rec st m)) (Some m))); [| rewrite cb_upd_meta, cb_set_head; reflexivity].
  rewrite cb_upd_meta.
  set (st1 := match m_prev (get_meta_rec st m) with Some pv => upd_meta pv (m_set_next (m_next (get_meta_rec st m))) st | None => st end).
  set (st2 := match m_next (get_meta_rec st m) with Some nx => upd_meta nx (m_set_prev (m_prev (get_meta_rec st m))) st1 | None => st1 end).
  assert (E1 : cb st1 = cb st) by (subst st1; destruct (m_prev (get_meta_rec st m)); reflexivity).
  assert (E2 : cb st2 = cb st1) by (subst st2; destruct (m_next (get_meta_rec st m)); reflexivity).
  destruct (optr_eqb (get_head st2 (h)) (Some m)); [rewrite cb_set_head|]; congruence.
Qed.

Section CBQ.
Context {T : Type}.
Implicit Types (Q : M T -> Prop).

Lemma cb_guard Q tag c (k bail : M T) : Q k -> (forall e h, Q (SVis (EUndef e) h)) -> Q (guard tag c k bail).
Proof. intros HK HU. unfold guard. destruct c; auto. Qed.

Lemma cb_queue Q h m st (k : mstate -> M T) bail :
  (forall st', cb st' = cb st -> Q (k st')) -> (forall e hh, Q (SVis (EUndef e) hh)) -> Q (queue h m st k bail).
Proof.
  intros HK HU. unfold queue. apply cb_guard; [| exact HU]. apply cb_guard; [| exact HU].
  destruct (get_head st h) as [hd|].
  - apply HK. rewrite cb_upd_meta. destruct (m_prev (get_meta_rec st hd)); rewrite ?cb_upd_meta; reflexivity.
  - apply HK. rewrite cb_set_head, cb_upd_meta. reflexivity.
Qed.

Lemma cb_free_meta Q m st (k : mstate -> M T) bail :
  (forall st', cb st' = cb st -> Q (k st')) -> (forall e hh, Q (SVis (EUndef e) hh)) -> Q (free_meta m st k bail).
Proof. intros HK HU. unfold free_meta. apply cb_queue; [| exact HU]. intros st' E. apply HK. rewrite E. apply cb_put_meta. Qed.

Lemma cb_activate_group Q m st (k : mstate -> Z -> M T) bail :
  (forall st' v, cb st' = cb st -> Q (k st' v)) -> (forall e hh, Q (SVis (EUndef e) hh)) -> Q (activate_group m st k bail).
Proof. intros HK HU. unfold activate_group. apply cb_guard; [| exact HU]. apply HK. apply cb_upd_meta. Qed.

Lemma cb_free_group Q (rec : mstate -> aptr -> Z -> (mstate -> mapinfo -> M T) -> M T -> M T) st g (k : mstate -> mapinfo -> M T) bail :
  (forall st1 m idx (k1 : mstate -> mapinfo -> M T) (Q1 : M T -> Prop),
      (forall st' mi, cb st' = cb st1 -> Q1 (k1 st' mi)) -> Q1 bail -> (forall e hh, Q1 (SVis (EUndef e) hh)) -> Q1 (rec st1 m idx k1 bail)) ->
  (forall st' mi, cb st' = cb st -> Q (k st' mi)) -> Q bail -> (forall e hh, Q (SVis (EUndef e) hh)) ->
  Q (free_group T dec_slots rec st g k bail).
Proof.
  intros HR HK HB HU. unfold free_group.
  set (st1 := if m_sizeclass (get_meta_rec st g) <? 48 then _ else st).
  assert (E1 : cb st1 = cb st) by (subst st1; destruct (m_sizeclass (get_meta_rec st g) <? 48); [apply cb_set_usage| reflexivity]).
  destruct (m_mem (get_meta_rec st g)) as [p|]; [| apply HU].
  set (st2 := del_slots p _ _ (del_group p st1)).
  assert (E2 : cb st2 = cb st) by (subst st2; rewrite cb_del_slots, cb_del_group; exact E1).
  destruct (negb (m_maplen (get_meta_rec st g) =? 0)).
  - apply cb_free_meta; [| exact HU]. intros st' E. apply HK. rewrite E, cb_record_seq, cb_step_seq. exact E2.
  - unfold dec_slots. destruct (s_slots st2 !! p) as [[m idx]|]; [| apply HU].
    apply HR; [| exact HB| exact HU]. intros st' mi E. apply cb_free_meta; [| exact HU]. intros st'' E'. apply HK. congruence.
Qed.

Theorem ntf_cb f : forall st g i (k : mstate -> mapinfo -> M T) bail Q,
  (forall st' mi, cb st' = cb st -> Q (k st' mi)) -> Q bail -> (forall e hh, Q (SVis (EUndef e) hh)) ->
  Q (nontrivial_free dec_slots f st g i k bail).
Proof.
  induction f as [|f IH]; intros st g i k bail Q HK HB HU; [apply HU|].
  cbn [nontrivial_free].
  destruct ((Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) + bit i =? mask_upto (m_last_idx (get_meta_rec st g))) && okay_to_free st g).
  - destruct (m_next (get_meta_rec st g)) as [nx|].
    + apply cb_guard; [| exact HU].
      set (st1 := dequeue _ g st). assert (E1 : cb st1 = cb st) by (subst st1; apply cb_dequeue).
      destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)); [destruct (active st1 (m_sizeclass (get_meta_rec st g))) as [a|]|].
      * apply cb_activate_group; [| exact HU]. intros st2 v E2. apply (cb_free_group Q); [intros; eapply IH; eassumption| intros st' mi E; apply HK; congruence| exact HB| exact HU].
      * apply (cb_free_group Q); [intros; eapply IH; eassumption| intros st' mi E; apply HK; congruence| exact HB| exact HU].
      * apply (cb_free_group Q); [intros; eapply IH; eassumption| intros st' mi E; apply HK; congruence| exact HB| exact HU].
    + apply (cb_free_group Q); [intros; eapply IH; eassumption| exact HK| exact HB| exact HU].
  - destruct (Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) =? 0).
    + apply cb_guard; [| exact HU].
      destruct (negb (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g))).
      * apply cb_queue; [| exact HU]. intros st' E. apply HK. rewrite cb_upd_meta. exact E.
      * apply HK. apply cb_upd_meta.
    + apply HK. apply cb_upd_meta.
Qed.
End CBQ.

Lemma ret_inj {A} (x y : A) : (ret x : M A) = ret y -> x = y.
Proof. intros E. injection E as E1. exact E1. Qed.

Lemma ntf_cb_eq f st g i (K : mstate -> mapinfo -> M mstate) st' mi :
  nontrivial_free dec_slots f st g i K (K st None) = K st' mi ->
  (forall st1 st2 mi1 mi2, K st1 mi1 = K st2 mi2 -> cb st1 = cb st2) ->
  (forall st2 mi2 e hh, K st2 mi2 <> SVis (EUndef e) hh) ->
  cb st' = cb st.
Proof.
  intros EQ KINJ NU.
  pose proof (ntf_cb f st g i K (K st None) (fun t => t = K st' mi -> cb st' = cb st)) as H. cbv beta in H.
  apply H; [| intros E; symmetry; exact (KINJ _ _ _ _ E)| intros e hh E; exfalso; exact (NU _ _ e hh (eq_sym E))| exact EQ].
  intros st1 mi1 E1 E2. rewrite <- E1. symmetry. exact (KINJ _ _ _ _ E2).
Qed.


Lemma mask_le0_zero x : 0 <= x -> (forall i, 0 <= i -> Z.testbit x i = true -> i <= 0) -> Z.testbit x 0 = false -> x = 0.
Proof.
  intros Hx Hb H0. apply Z.bits_inj_0. intros j.
  destruct (Z_lt_dec j 0) as [Hn|Hn]; [apply Z.testbit_neg_r; lia|].
  destruct (Z.testbit x j) eqn:E; [| reflexivity]. exfalso.
  pose proof (Hb j ltac:(lia) E). assert (j = 0) by lia. subst j. rewrite H0 in E. discriminate.
Qed.

Lemma geom_same_geo r1 r0 : geom r1 = geom r0 -> same_geo r1 r0.
Proof. unfold geom, same_geo. intros E. inversion E. repeat split; assumption. Qed.

Section FREE.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (c : cptr) (off n : Z) (X : list blk) (k : Z) (xb : blk).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis Hk : In ((c, off), n) BL.
Hypothesis F0 : FF (xb :: X) k st.
Hypothesis Hxb : bslot xb = c.

Theorem free_FF : ftree L (free st (Some (aadd c (UNIT * off)))) (fun L' st' => FF X k st').
Proof.
  pose proof (free_INVL_closed st L BL LS c off n INV Hk) as FT.
  destruct (free_prefix st L BL LS c off n INV Hk) as (m & bm & i & FH & CE1 & STR1 & Hs & INV1 & Hm1 & Hi & Ec & NA & NF & SC & AGREE).
  cbn zeta in FH, INV1, Hm1, Hi, Ec, NA, NF, SC, AGREE.
  set (p := aadd c (UNIT * off)) in *. set (st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st)) in *.
  unfold free in FT |- *. rewrite FH in FT |- *. cbn [sbind] in FT |- *.
  assert (MR1 : forall x, MR st1 x = MR st x) by (intros; apply MR_ext; exact (ce_metas _ _ CE1)).
  assert (F1 : FF (xb :: X) k st1) by exact (FF_ctrl _ _ st st1 CE1 F0).
  pose proof INV1 as (IR1 & IA1 & IM1 & IL1 & IG1 & IS1 & ISH1).
  destruct Hm1 as [ai Hg1].
  pose proof (ig_ok _ _ _ IG1 _ _ _ Hg1) as GO1.
  pose proof (g_masks _ _ _ _ _ _ GO1) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_li _ _ _ _ _ _ GO1) as LI. pose proof (g_ai _ _ _ _ _ _ GO1) as AI.
  assert (KS : forall b0 m0, hosts st1 b0 m0 -> slot_start' (MR st1 m0) 0 = c -> m0 = m /\ i = 0).
  { intros b0 m0 Hh E0. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG1 _ _ _ (proj2_sig_of_ex Hh))) as LI0 || pose proof I as LI0.
    destruct Hh as [ai0 Hb0]. pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG1 _ _ _ Hb0)) as LI0'.
    pose proof (is_total _ _ _ IS1 b0 m0 0 (ex_intro _ ai0 Hb0) ltac:(lia)) as T. rewrite E0 in T.
    rewrite (ce_slots _ _ CE1), Hs in T. inversion T. split; reflexivity. }
  assert (KM : KCLS (m_sizeclass (MR st1 m)) ->
            m_last_idx (MR st1 m) = 0 /\ i = 0 /\ m_freed (MR st1 m) = 0 /\ m_avail (MR st1 m) = 0 /\ m_maplen (MR st1 m) <> 0).
  { intros HK. destruct (proj1 F1 _ _ _ Hg1) as [_ KK]. destruct (KK HK) as [L0 _].
    assert (Hi0 : i = 0) by lia. unfold tbit in NA, NF. rewrite Hi0 in NA, NF.
    assert (FZ : m_freed (MR st1 m) = 0) by (apply mask_le0_zero; [exact M2| intros j Hj Hb; pose proof (M4 j Hj Hb); lia| exact NF]).
    assert (AZ : m_avail (MR st1 m) = 0) by (apply mask_le0_zero; [exact M1| intros j Hj Hb; pose proof (M3 j Hj Hb); lia| exact NA]).
    pose proof (KCLS_range _ HK) as (R1 & _).
    destruct (g_stride _ _ _ _ _ _ GO1 ltac:(lia)) as (_ & ML & _).
    split; [exact L0|]. split; [exact Hi0|]. split; [exact FZ|]. split; [exact AZ| exact (proj1 (ML L0))]. }
  assert (TESTK : KCLS (m_sizeclass (MR st1 m)) ->
            (Z.lor (m_freed (MR st1 m)) (m_avail (MR st1 m)) + bit i =? mask_upto (m_last_idx (MR st1 m))) && okay_to_free st1 m = true).
  { intros HK. destruct (KM HK) as (L0 & Hi0 & FZ & AZ & ML). rewrite FZ, AZ, L0, Hi0. change (Z.lor 0 0 + bit 0 =? mask_upto 0) with true. cbn [andb].
    unfold okay_to_free. change (get_meta_rec st1 m) with (MR st1 m). rewrite (g_freeable _ _ _ _ _ _ GO1). cbn [Z.eqb Pos.eqb].
    destruct ((48 <=? m_sizeclass (MR st1 m)) || (get_stride (MR st1 m) <? UNIT * size_class (m_sizeclass (MR st1 m)))); [reflexivity|].
    replace (m_maplen (MR st1 m) =? 0) with false by (symmetry; apply Z.eqb_neq; exact ML).
    destruct (negb (optr_eqb (m_next (MR st1 m)) (Some m))); [reflexivity|].
    destruct F1 as [_ [_ B99]].
    destruct HK as [E|[E|E]]; rewrite E; [| reflexivity| reflexivity].
    replace (is_bouncing 31 st1) with (100 <=? bounces st1 24) by reflexivity.
    replace (100 <=? bounces st1 24) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
  unfold free_tail in FT |- *. change (get_meta_rec st1 m) with (MR st1 m) in FT |- *.
  apply ftree_guard_inv in FT as [GC FT]. apply ftree_guard; [exact GC|].
  destruct (negb ((m_freed (MR st1 m) =? 0) || (Z.lor (m_freed (MR st1 m)) (m_avail (MR st1 m)) + bit i =? mask_upto (m_last_idx (MR st1 m))))) eqn:BR.
  -
    apply ftree_ret. apply (FF_free X k st1 _ xb F1); [| rewrite (cb_bounces st1) by apply cb_upd_meta; lia].
    intros b0 m0 ai0 Hb0. change (s_groups st1 !! b0 = Some (mkGhdr (Some m0) ai0)) in Hb0.
    assert (SG : same_geo (MR (upd_meta m (m_set_freed (m_freed (MR st1 m) + bit i)) st1) m0) (MR st1 m0)).
    { unfold MR. destruct (decide (m0 = m)) as [->|NE]; [rewrite get_meta_rec_upd_same; apply same_geo_set_freed| rewrite get_meta_rec_upd_other by exact NE; apply same_geo_refl]. }
    split; [split; [exists ai0; exact Hb0| exact SG]|].
    intros HK E0. destruct SG as (_ & _ & _ & ESC). rewrite ESC in HK. rewrite Hxb in E0.
    destruct (KS b0 m0 (ex_intro _ ai0 Hb0) E0) as [-> Hi0].
    destruct (KM HK) as (_ & _ & FZ & _). rewrite FZ, Z.eqb_refl in BR. cbn [orb negb] in BR. discriminate BR.
  -
    set (K := fun (st2 : mstate) (mi : mapinfo) => match mi with
          | Some (base, len) => if negb (len =? 0) then SVis (EMunmap (conc st2 base) len) (fun ru : Z => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st1)) else ret st2
          | None => ret st2 end) in FT |- *.
    destruct (ntf_allQ mstate FUEL dec_hdr dec_slots (dec_hdr_ok mstate) (dec_slots_ok mstate) (xpend x0 (Some c)) st1 L (bl_remove c BL) LS m bm i K (ret st1)
                INV1 (ex_intro _ ai Hg1) Hi ltac:(cbn; rewrite Ec; reflexivity) eq_refl eq_refl ltac:(unfold FUEL; lia) ltac:(unfold FUEL; lia))
      as (st' & mi & LS' & EQ & EQ2 & [RG SEC] & [F CASE] & POST).
    rewrite EQ in FT |- *.
    assert (CB : cb st' = cb st1).
    { apply (ntf_cb_eq FUEL st1 m i K st' mi); [exact EQ2| |].
      - intros sa sb mia mib E. unfold K in E. destruct mia as [[ba la]|], mib as [[bb lb]|]; cbv beta iota in E.
        + destruct (negb (la =? 0)), (negb (lb =? 0)); try discriminate E.
          * injection E as Q1 Q2 Q3. pose proof (f_equal (fun h => h 0) Q3) as E0. cbv beta in E0.
            change (ret (drop_region (fst ba) sa) = ret (drop_region (fst bb) sb)) in E0.
            exact (f_equal cb (ret_inj _ _ E0)).
          * exact (f_equal cb (ret_inj _ _ E)).
        + destruct (negb (la =? 0)); [discriminate E|]. exact (f_equal cb (ret_inj _ _ E)).
        + destruct (negb (lb =? 0)); [discriminate E|]. exact (f_equal cb (ret_inj _ _ E)).
        + exact (f_equal cb (ret_inj _ _ E)).
      - intros sa mia e hh E. unfold K in E. destruct mia as [[ba la]|]; [destruct (negb (la =? 0)); discriminate E| discriminate E]. }
    assert (IM' : exists X' L2 LS2, INVL X' st' L2 (bl_remove c BL) LS2).
    { destruct mi as [[base len]|]; [destruct POST as (r & _ & _ & _ & _ & _ & INV')| rename POST into INV']; eexists _, _, _; exact INV'. }
    destruct IM' as (X' & L2 & LS2 & INV'). pose proof (proj1 (proj2 (proj2 INV'))) as IM2.
    assert (F' : FF X k st').
    { apply (FF_free X k st1 _ xb F1); [| rewrite (cb_bounces st1 st' 24 CB); lia].
      intros b0 m0 ai0 Hb0.
      destruct (ffr_groups _ _ F b0 _ Hb0) as ([gm ga] & H10 & Egm). cbn in Egm. subst gm.
      assert (SG : same_geo (MR st' m0) (MR st1 m0)).
      { destruct (ffr_meta _ _ F m0) as [G|[Z0 _]]; [exact (geom_same_geo _ _ G)|].
        exfalso. destruct (im_hdr _ _ _ IM2 _ _ Hb0) as (m' & Em & MEM & _). cbn in Em. assert (m' = m0) by congruence. subst m'.
        unfold MR in Z0. rewrite Z0 in MEM. discriminate MEM. }
      split; [split; [exists ga; exact H10| exact SG]|].
      intros HK E0. destruct SG as (_ & _ & _ & ESC). rewrite ESC in HK. rewrite Hxb in E0.
      destruct (KS b0 m0 (ex_intro _ ga H10) E0) as [-> Hi0].
      assert (Eb : b0 = bm).
      { destruct (im_hdr _ _ _ IM1 _ _ H10) as (m1 & Em1 & MEM1 & _). cbn in Em1. assert (m1 = m) by congruence. subst m1.
        destruct (im_hdr _ _ _ IM1 _ _ Hg1) as (m2 & Em2 & MEM2 & _). cbn in Em2. assert (m2 = m) by congruence. subst m2. congruence. }
      subst b0. destruct CASE as [GONE|(_ & _ & TF)]; [rewrite GONE in Hb0; discriminate Hb0|].
      rewrite (TESTK HK) in TF. discriminate TF. }
    destruct mi as [[base len]|].
    + destruct POST as (r & Hb0 & Hr & Kr & Elen & Lpos & _). cbn [K] in FT |- *.
      replace (negb (len =? 0)) with true in FT |- * by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
      cbn [ftree] in FT. destruct FT as [PRE FK].
      apply ftree_vis; [reflexivity| reflexivity| exact PRE| |].
      * intros a Ha. specialize (FK a). rewrite Ha in FK. cbn [answer_ok] in Ha. rewrite Ha in FK |- *.
        apply ftree_ret. apply FF_drop_region. exact F'.
      * intros a Ha. cbn [answer_ok] in Ha. rewrite Ha. exact I.
    + cbn [K]. apply ftree_ret. exact F'.
Qed.
End FREE.
