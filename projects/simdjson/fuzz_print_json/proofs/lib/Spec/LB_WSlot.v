(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation FinFun.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Decode.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import STree Malloc MallocCtrl KInv KStep
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry MI_WTry2 MI_WGroup MI_Cnt MI_TF2 MI_WCreate2 MI_WSlot MI_WSlot2 MI_WSlot3
  LB_Tables LB_Inv LB_Sum LB_Kernel LB_Embed LB_Bound LB_WNtf LB_XferF LB_Tree LB_QM LB_WAMeta LB_WTry LB_Cnt LB_AG LB_WFree.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Unforced.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition QPOST (P : Z -> Z) (idle : list aptr) (BL : list blk) (st : mstate) : Prop :=
  SG st BL /\ QM (X_as idle) st 0 /\ AQ st BL P.

Lemma QPOST_SINV P idle BL st X : x_idle X = idle -> QPOST P idle BL st -> SINV X st BL /\ AQ st BL P.
Proof. intros E (S & Q & A). split; [| exact A]. apply SINV_split. split; [exact S|]. apply (QM_X (X_as idle)); [rewrite E; reflexivity| exact Q]. Qed.

Lemma SINV_QPOST P idle BL st X : x_idle X = idle -> SINV X st BL -> AQ st BL P -> QPOST P idle BL st.
Proof. intros E S A. apply SINV_split in S as [S Q]. split; [exact S|]. split; [| exact A]. apply (QM_X X); [cbn; symmetry; exact E| exact Q]. Qed.

Record qsame (st st1 : mstate) : Prop := mkQS {
  qs_groups : s_groups st1 = s_groups st;
  qs_slots : s_slots st1 = s_slots st;
  qs_metas : s_metas st1 = s_metas st;
  qs_regions : s_regions st1 = s_regions st;
  qs_amc : c_avail_meta_count (s_ctx st1) = c_avail_meta_count (s_ctx st);
  qs_amas : c_avail_meta_areas (s_ctx st1) = c_avail_meta_areas (s_ctx st);
  qs_shift : c_meta_alloc_shift (s_ctx st1) = c_meta_alloc_shift (s_ctx st) }.

Lemma QPOST_qsame P idle BL st st1 X L LS : INVL X st L BL LS -> qsame st st1 -> QPOST P idle BL st -> QPOST P idle BL st1.
Proof.
  intros INV [EG ES EM ER EC EA EH] (S & Q & A).
  assert (MRx : forall x, MR st1 x = MR st x) by (intros x; unfold MR, get_meta_rec; rewrite EM; reflexivity).
  assert (GEO : forall x, (exists b, hosts st b x) -> geom (MR st1 x) = geom (MR st x)) by (intros x _; rewrite MRx; reflexivity).
  split; [| split].
  - apply (SG_frame st st1 BL EG ES GEO); [| exact S]. intros s x i Hs. exact (proj1 (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ _ Hs)).
  - destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. constructor; rewrite ?EM, ?ER, ?EC, ?EH, ?(ncarved_ext st st1 EM), ?(apages_ext st st1 ER EA); auto.
  - apply (AQ_frame st st1 BL P EG GEO); [rewrite (ncarved_ext st st1 EM); exact (aq_carved _ _ _ A)| exact A].
Qed.

Lemma qsame_step_seq st : qsame st (step_seq st).
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); constructor; reflexivity. Qed.
Lemma qsame_account_bounce sc st : qsame st (account_bounce sc st).
Proof. unfold account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; constructor; reflexivity. Qed.
Lemma qsame_trans a b c : qsame a b -> qsame b c -> qsame a c.
Proof. intros [A1 A2 A3 A4 A5 A6 A7] [B1 B2 B3 B4 B5 B6 B7]; constructor; congruence. Qed.

Definition BLF (st0 st1 : mstate) (BL : list blk) : Prop :=
  forall k, In k BL -> slotcls st1 (bslot k) = slotcls st0 (bslot k).
Lemma BLF_refl st BL : BLF st st BL.
Proof. intros k _. reflexivity. Qed.
Lemma BLF_trans a b c BL : BLF a b BL -> BLF b c BL -> BLF a c BL.
Proof. intros H1 H2 k Hk. rewrite (H2 k Hk). exact (H1 k Hk). Qed.
Lemma scl_geo X st st1 L BL LS : INVL X st L BL LS -> s_slots st1 = s_slots st ->
  (forall m, (exists b, hosts st b m) -> geom (MR st1 m) = geom (MR st m)) -> forall s, slotcls st1 s = slotcls st s.
Proof.
  intros INV ES GEO s. unfold slotcls, cls. rewrite ES. destruct (s_slots st !! s) as [[m i]|] eqn:E; [| reflexivity].
  pose proof (GEO m (proj1 (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ _ E))) as G.
  unfold geom in G. inversion G. reflexivity.
Qed.
Lemma BLF_geo X st st1 L BL LS : INVL X st L BL LS -> s_slots st1 = s_slots st ->
  (forall m, (exists b, hosts st b m) -> geom (MR st1 m) = geom (MR st m)) -> BLF st st1 BL.
Proof. intros INV ES GEO k _. exact (scl_geo X st st1 L BL LS INV ES GEO (bslot k)). Qed.
Lemma BLF_qsame st st1 BL : qsame st st1 -> BLF st st1 BL.
Proof. intros [_ ES EM _ _ _ _] k _. unfold slotcls, cls, MR, get_meta_rec. rewrite ES, EM. reflexivity. Qed.
Lemma BLF_ffr X2 st1 st2 L2 BL LS2 : INVL X2 st2 L2 BL LS2 -> FFR st1 st2 -> BLF st1 st2 BL.
Proof. intros INV F k Hk. exact (x_slotcls X2 st1 st2 L2 BL LS2 INV F k Hk). Qed.
Lemma BLF_old X st0 st1 L BL LS : INVL X st0 L BL LS -> (forall s, s_slots st0 !! s <> None -> slotcls st1 s = slotcls st0 s) -> BLF st0 st1 BL.
Proof.
  intros INV H k Hk. apply H. destruct (is_blocks _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) k Hk) as (x & i & Hs & _). rewrite Hs. discriminate.
Qed.
Lemma BLF_MIS st0 st1 BL c : BLF st0 st1 BL -> MIS st1 BL c = MIS st0 BL c.
Proof. intros H. unfold MIS. apply zcount_ext. intros k Hk. rewrite (H k Hk). reflexivity. Qed.
Lemma BLF_LS st0 st1 BL c : BLF st0 st1 BL -> LS st1 BL c = LS st0 BL c.
Proof. intros H. unfold LS. apply zcount_ext. intros k Hk. rewrite (H k Hk). reflexivity. Qed.
Lemma qsame_upd_ctx st f :
  (forall c, c_avail_meta_count (f c) = c_avail_meta_count c) -> (forall c, c_avail_meta_areas (f c) = c_avail_meta_areas c) ->
  (forall c, c_meta_alloc_shift (f c) = c_meta_alloc_shift c) -> qsame st (upd_ctx f st).
Proof. intros H1 H2 H3. constructor; cbn; auto. Qed.

Lemma free_idle_q idle m st L BL LS P : INVL (X_as (m :: idle)) st L BL LS -> ~ In m idle ->
  QPOST P (m :: idle) BL st -> QPOST P idle BL (fm_st st m).
Proof.
  intros INV NIm (S & Q & A).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (fi_metas idle m st L BL LS INV) as Hm.
  assert (PUT : put_meta m meta0 st = st) by (apply (fi_put idle m st L BL LS INV)).
  unfold fm_st. rewrite PUT.
  destruct (queue_frame LFree m st) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
  pose proof (queue_data LFree m st) as DD.
  assert (GEO : forall x, (exists b, hosts st b x) -> geom (MR (queue_st LFree m st) x) = geom (MR st x)) by (intros x _; apply geom_data; apply DD).

  assert (DOM : forall x, s_metas (queue_st LFree m st) !! x <> None <-> s_metas st !! x <> None).
  { intros x. split; [| apply queue_keys_mono]. intros Hx. destruct (queue_keys LFree m st x Hx) as [H'|[->|[Hh|(a & Hh & Hpv)]]]; [exact H'| rewrite Hm; discriminate| |].
    - apply (listed_present _ _ _ _ _ INV x LFree). exact (head_listed _ _ _ _ _ INV LFree x Hh).
    - apply (listed_present _ _ _ _ _ INV x LFree). exact (prev_listed _ _ _ _ _ INV LFree a x (head_listed _ _ _ _ _ INV LFree a Hh) Hpv). }
  pose proof (ncarved_dom st (queue_st LFree m st) DOM) as NC.
  split; [| split].
  - apply (SG_frame st _ BL F5 F6 GEO); [| exact S]. intros s x i Hs. exact (proj1 (is_valid _ _ _ IS _ _ _ Hs)).
  - destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. destruct FC. constructor; rewrite ?F1, ?NC; auto.
    + intros x mr Hx Z0.
      assert (Px : s_metas st !! x <> None) by (apply DOM; rewrite Hx; discriminate).
      destruct (s_metas st !! x) as [mr0|] eqn:E0; [| congruence].
      pose proof (DD x) as Dx. rewrite (MR_of_lookup _ _ _ Hx), (MR_of_lookup _ _ _ E0) in Dx. apply data_of_eq in Dx as (Em & _).
      pose proof (queue_next LFree m st x) as QN. rewrite (MR_of_lookup _ _ _ Hx) in QN.
      destruct (aptr_eq_dec x m) as [->|NE].
      * left. rewrite QN. cbn [get_head]. destruct (c_free_meta_head (ctx st)) as [a|] eqn:HH.
        -- destruct (aptr_eqb_spec m a) as [->|NEa].
           { exfalso. apply (proj2 (im_idle _ _ _ IM a ltac:(left; reflexivity))). exists LFree. exact (head_listed _ _ _ _ _ INV LFree a HH). }
           destruct (optr_eqb _ _); [discriminate|]. rewrite aptr_eqb_refl. discriminate.
        -- rewrite aptr_eqb_refl. discriminate.
      * destruct (Q1 x mr0 E0 ltac:(congruence)) as [N0|I0].
        -- left. rewrite QN. cbn [get_head]. destruct (c_free_meta_head (ctx st)) as [a|].
           ++ destruct (aptr_eqb_spec x a) as [->|NEa].
              ** destruct (optr_eqb _ _); [discriminate|]. destruct (aptr_eqb_spec a m); [congruence|]. rewrite (MR_of_lookup _ _ _ E0). exact N0.
              ** destruct (optr_eqb _ _); [discriminate|]. destruct (aptr_eqb_spec x m); [congruence|]. rewrite (MR_of_lookup _ _ _ E0). exact N0.
           ++ destruct (aptr_eqb_spec x m); [congruence|]. rewrite (MR_of_lookup _ _ _ E0). exact N0.
        -- destruct I0 as [->|I1]; [congruence| right; exact I1].
    + rewrite (apages_ext st (queue_st LFree m st) F1 cb_amas), cb_amc. exact Q2.
    + rewrite cb_shift. exact Q4.
    + rewrite cb_shift. exact Q6.
  - apply (AQ_frame st _ BL P F5 GEO); [rewrite NC; exact (aq_carved _ _ _ A)| exact A].
Qed.

Lemma BLF_free_idle idle m st L BL LS : INVL (X_as (m :: idle)) st L BL LS -> BLF st (fm_st st m) BL.
Proof.
  intros INV. apply (BLF_geo _ st _ L BL LS INV).
  - unfold fm_st. rewrite (fi_put idle m st L BL LS INV). destruct (queue_frame LFree m st) as (_ & _ & _ & _ & _ & F6 & _). exact F6.
  - intros x _. apply geom_data. unfold fm_st. rewrite (fi_put idle m st L BL LS INV). apply queue_data.
Qed.

Lemma state_bytes_B X st L BL LS P B : INVL X st L BL LS -> x_pend X = None -> x_orph X = None ->
  SINV X st BL -> AQ st BL P -> PHI P + R63 BL <= B + 3 * PGSZ -> gm L + BB L <= B.
Proof.
  intros INV HP HO SI HAQ HB. pose proof (ledger_bound X st L BL LS INV) as L1. pose proof (regions_bound X st L BL LS P INV SI HAQ HP) as R1.
  unfold ORPH in R1. rewrite HO in R1. unfold PGSZ in *. lia.
Qed.

Lemma group_bytes_B X st L BL LS P B : INVL X st L BL LS -> x_pend X = None -> x_orph X = None ->
  SINV X st BL -> AQ st BL P -> PHI P + R63 BL <= B + 3 * PGSZ -> group_bytes st + PGSZ * (5 * NCAP P / 101 + 8) <= B.
Proof.
  intros INV HP HO SI HAQ HB. pose proof (group_bytes_bound X st L BL LS P INV SI HAQ HP) as R1.
  unfold ORPH in R1. rewrite HO in R1. unfold PGSZ in *. lia.
Qed.

Definition AGK (T : Type) (P : Z -> Z) (B : Z) (Post : mled -> T -> Prop) (idle : list aptr) (sc req : Z) (st0 : mstate) (L0 : mled) (BL : list blk)
  (k : mstate -> optr -> M T) : Prop :=
  forall st2 go L2 LS2, AG_POST idle sc req st0 L0 BL st2 go L2 LS2 -> QPOST P idle BL st2 ->
  (forall c, 0 <= c < sc -> gcnt st2 c <= gcnt st0 c) -> BLF st0 st2 BL -> fqtree B L2 (k st2 go) Post.

Lemma QPOST_new_group_region P idle BL st X L LS a len :
  INVL X st L BL LS -> QPOST P idle BL st -> QPOST P idle BL (fst (new_region RKGroup a len st)).
Proof.
  intros INV (S & Q & A). pose proof (nm_fresh _ _ _ _ _ INV) as FR.
  set (st2 := fst (new_region RKGroup a len st)).
  assert (MRx : forall x, MR st2 x = MR st x) by (intros; reflexivity).
  assert (GEO : forall x, (exists b, hosts st b x) -> geom (MR st2 x) = geom (MR st x)) by (intros; reflexivity).
  assert (RG : s_regions st2 = <[s_next_rid st := mkRegion RKGroup a len]> (s_regions st)) by reflexivity.
  assert (AP : apages st2 = apages st).
  { rewrite !apages_msum, RG, (msum_insert _ _ _ _ FR). unfold apF at 1. cbn [fst snd is_metakind_b r_kind]. rewrite Z.add_0_l.
    apply msum_ext. intros q rq Hq. unfold apF, frontier. cbn. reflexivity. }
  split; [| split].
  - apply (SG_frame st st2 BL eq_refl eq_refl GEO); [| exact S]. intros s x i Hs. exact (proj1 (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) _ _ _ Hs)).
  - destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]. constructor; try exact Q1; rewrite ?RG, ?AP; change (ncarved st2) with (ncarved st); change (s_ctx st2) with (s_ctx st); auto.
    + intros q rq Hq K. destruct (N.eq_dec q (s_next_rid st)) as [->|NE]; [rewrite lookup_insert_eq in Hq; inversion Hq; subst; cbn in K; discriminate|].
      rewrite lookup_insert_ne in Hq by congruence. exact (Q3 q rq Hq K).
    + intros q rq Hq K. destruct (N.eq_dec q (s_next_rid st)) as [->|NE]; [rewrite lookup_insert_eq in Hq; inversion Hq; subst; cbn in K; discriminate|].
      rewrite lookup_insert_ne in Hq by congruence. exact (Q4 q rq Hq K).
    + intros q1 q2 r1 r2 H1 H2 K1 K2 NE.
      destruct (N.eq_dec q1 (s_next_rid st)) as [->|NE1]; [rewrite lookup_insert_eq in H1; inversion H1; subst; cbn in K1; discriminate|].
      destruct (N.eq_dec q2 (s_next_rid st)) as [->|NE2]; [rewrite lookup_insert_eq in H2; inversion H2; subst; cbn in K2; discriminate|].
      rewrite lookup_insert_ne in H1 by congruence. rewrite lookup_insert_ne in H2 by congruence. exact (Q5 _ _ _ _ H1 H2 K1 K2 NE).
  - apply (AQ_frame st st2 BL P eq_refl GEO); [change (ncarved st2) with (ncarved st); exact (aq_carved _ _ _ A)| exact A].
Qed.

Section MMAP_BRANCHQ.
Variables (T : Type) (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr) (P : Z -> Z) (B : Z).
Variables (m : aptr) (sc req cnt needed : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis GRP : grp_ok sc cnt needed = true.
Hypothesis RED : (cnt = 1 /\ needed = round_up_pg (req + IB + UNIT) /\ 28 <= sc) \/ (UNIT * size_class sc * cnt + UNIT <= needed).
Hypothesis QP1 : QPOST P (m :: idle) BL st1.
Hypothesis STD : cnt = cmax sc -> needed = std_len sc /\ std_nested sc = false.
Hypothesis NSTD : cnt <> cmax sc -> gcnt st1 sc < 128.
Hypothesis NUB : needed <= UNIT * size_class sc * cnt + 4111.
Hypothesis GLE1 : forall c, gcnt st1 c = gcnt st0 c.
Hypothesis BF1 : BLF st0 st1 BL.
Hypothesis HBP : PHI P + R63 BL <= B + 3 * PGSZ.
Hypothesis HK : AGK T P B Post idle sc req st0 L0 BL k.
Let st1' := step_seq (account_bounce sc st1).
Let MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c.
Let AI := let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if cnt - 1 <? ai then cnt - 1 else ai in if ai <? 0 then 0 else ai.

Lemma QP1' : QPOST P (m :: idle) BL st1'.
Proof. apply (QPOST_qsame P (m :: idle) BL st1 st1' _ L1 LS1 INV1); [| exact QP1]. eapply qsame_trans; [apply qsame_account_bounce| apply qsame_step_seq]. Qed.

Lemma mmap_final a :
  let st1f := step_seq (account_bounce sc st1) in
  mmap_answer_ok (live_ranges st1f) needed a = true -> is_err a = false ->
  let st2 := fst (new_region RKGroup a needed st1f) in let rid := s_next_rid st1f in
  let stf := agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI in
  let mr' := agG sc (rid, 0) cnt AI (m_set_maplen (Z.shiftr needed 12) meta0) in
  INVL (mkX idle [] None None (Some m)) stf (KInv.set_groups ((a, needed) :: ld_groups L1) L1) BL LS1
  /\ TF0 stf /\ MR stf m = mr' /\ s_groups stf !! (rid, 0) = Some (mkGhdr (Some m) AI)
  /\ (forall sc0, active stf sc0 = active st0 sc0) /\ QPOST P idle BL stf
  /\ s_regions stf = s_regions st2 /\ s_secret st2 = s_secret st1 /\ (forall c, gcnt stf c = (if sc =? c then cnt else 0) + gcnt st1 c)
  /\ BLF st0 stf BL.
Proof.
  cbn zeta. intros Ha ER.
  destruct (st1'_facts idle st1 L1 BL LS1 m sc INV1 TF1) as (INV1' & SH1 & TK1 & ACT1 & TF1' & RG1 & SS1'). fold st1' in INV1', SH1, TK1, ACT1, TF1', RG1, SS1' |- *.
  pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  set (st2 := fst (new_region RKGroup a needed st1')). set (rid := s_next_rid st1').
  pose proof (INVL_new_group_region (X_as (m :: idle)) st1' L1 BL LS1 a needed INV1' eq_refl Ha ER ltac:(unfold LEN_MAX; lia)) as INV2.
  fold rid st2 in INV2. cbn [xorph X_as x_idle x_zomb x_pend x_fresh] in INV2.
  assert (Hr : s_regions st2 !! rid = Some (mkRegion RKGroup a needed)) by (unfold st2; rewrite ng_lookup; fold rid; rewrite N.eqb_refl; reflexivity).
  assert (NS : s_shadow st2 !! rid = None) by (unfold st2, rid; change (s_shadow (fst (new_region RKGroup a needed st1'))) with (s_shadow st1'); exact (shadow_next_rid_none _ _ _ _ _ INV1')).
  assert (ACT2 : forall sc', active st2 sc' = active st0 sc') by (intros sc'; unfold st2; change (active (fst (new_region RKGroup a needed st1')) sc') with (active st1' sc'); rewrite ACT1; apply HA1).
  assert (EMP : LS1 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT2; exact HA0).
  assert (TF2' : TF0 st2) by (apply (TF0_ctrl st1'); [reflexivity| reflexivity| exact TF1']).
  pose proof (clamp_ai (UNIT * size_class sc) cnt ltac:(lia)) as HAI. cbn zeta in HAI. fold AI in HAI.
  assert (HAI0 : sc = 0 -> AI = cnt - 1).
  { intros Hsc0. unfold AI. rewrite Hsc0. change (UNIT * size_class 0) with 16. change ((4096 - UNIT) / 16 - 1) with 254.
    replace (cnt - 1 <? 254) with true by (symmetry; apply Z.ltb_lt; lia). replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  destruct (ag_top_ok idle st2 (KInv.set_groups ((a, needed) :: ld_groups L1) L1) BL LS1 m rid (mkRegion RKGroup a needed) sc cnt needed AI
              INV2 Hr eq_refl eq_refl NS GRP Hsc HAI HAI0 EMP TF2' NIm) as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
  change (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) with (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) in *.
  split; [exact INV'|]. split; [exact TF'|]. split; [exact MR'|]. split; [exact GR'|]. split; [intros sc0; rewrite ACT'; apply ACT2|].
  enough (QG : QPOST P idle BL (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI)
              /\ (forall c, gcnt (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) c = (if sc =? c then cnt else 0) + gcnt st1 c)
              /\ BLF st0 (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) BL).
  { destruct QG as (QG1 & QG2 & QG3). split; [exact QG1|]. split; [rewrite agt_regions; reflexivity|]. split; [exact SS1'|]. split; [exact QG2| exact QG3]. }

  pose proof (top_facts rid sc cnt needed AI GRP Hsc) as TFX. cbn zeta in TFX.
  destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
  destruct (QPOST_new_group_region P (m :: idle) BL st1' _ L1 LS1 a needed INV1' QP1') as (SG2 & Q2 & A2). fold st2 in SG2, Q2, A2.
  pose proof INV2 as (IR2 & IA2 & IM2 & IL2 & IG2 & IS2 & ISH2).
  assert (FR : s_regions st1' !! rid = None) by (unfold rid; exact (nm_fresh _ _ _ _ _ INV1')).
  assert (HpN : s_groups st2 !! (rid, 0) = None).
  { destruct (s_groups st2 !! (rid, 0)) as [h|] eqn:E; [| reflexivity]. exfalso.
    change (s_groups st2) with (s_groups st1') in E. destruct (ig_region _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1'))))) _ _ E) as (r & Hr' & _). cbn in Hr'. rewrite FR in Hr'. discriminate. }
  assert (HsN : s_slots st2 !! (rid, 0) = None).
  { destruct (s_slots st2 !! (rid, 0)) as [[x i]|] eqn:E; [| reflexivity]. exfalso.
    change (s_slots st2) with (s_slots st1') in E. destruct (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV1')))))) _ _ _ E) as ([b [aix Hb]] & _ & Es).
    destruct (ig_region _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1'))))) _ _ Hb) as (r & Hr' & _).
    pose proof (hosts_mem _ _ _ (proj1 (proj2 (proj2 INV1'))) _ _ (ex_intro _ aix Hb)) as MM.
    unfold slot_start', gbase in Es. rewrite MM in Es. cbn in Es. assert (E1 : fst b = rid) by (inversion Es; reflexivity). rewrite E1, FR in Hr'. discriminate. }
  assert (NEEDED : Z.shiftr needed 12 * 4096 = needed) by (rewrite F10; apply round_up_pg_id; exact G2).
  assert (STRIDE : get_stride (agG sc (rid, 0) cnt AI (m_set_maplen (Z.shiftr needed 12) meta0)) = if (cnt - 1 =? 0) then Z.shiftr needed 12 * 4096 - UNIT else UNIT * size_class sc).
  { rewrite Emr. unfold get_stride. cbn -[Z.shiftr Z.mul Z.sub Z.eqb size_class]. replace (Z.shiftr needed 12 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite andb_true_r. reflexivity. }
  pose proof (tab_basic_ok sc Hsc) as (_ & CM & _).
  set (stA := upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) in *.
  assert (LKm : forall x, x <> m -> s_metas stA !! x = s_metas st2 !! x) by (intros x NE; unfold stA; rewrite s_metas_upd_meta, lookup_insert_ne by congruence; reflexivity).
  assert (LKc : c_avail_meta_count (s_ctx stA) = c_avail_meta_count (s_ctx st2) /\ c_avail_meta_areas (s_ctx stA) = c_avail_meta_areas (s_ctx st2)
                /\ c_meta_alloc_shift (s_ctx stA) = c_meta_alloc_shift (s_ctx st2)) by (repeat split; reflexivity).
  assert (HmA : s_metas stA !! m <> None) by (unfold stA; rewrite s_metas_upd_meta, lookup_insert_eq; discriminate).
  assert (HmI : s_metas st2 !! m = Some meta0) by exact (proj1 (im_idle _ _ _ IM2 m ltac:(left; reflexivity))).
  assert (ROOM : gcnt st2 sc <= CAP P sc) by (apply (creation_room _ st2 _ BL LS1 P INV2 SG2 A2 sc Hsc eq_refl); rewrite ACT2; exact HA0).
  assert (NEWG : m_sizeclass (MR (agt stA sc m (rid, 0) cnt AI) m) = sc /\ m_last_idx (MR (agt stA sc m (rid, 0) cnt AI) m) = cnt - 1) by (rewrite MR', Emr; split; reflexivity).
  assert (QGm : m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) <> 0 -> m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) * 4096 <= cnt * S_ sc + 4111 /\ s_slots st2 !! (rid, 0) = None).
  { rewrite MR', Emr. cbn [m_maplen]. intros _. split; [| exact HsN]. unfold S_. rewrite NEEDED. lia. }
  assert (QGn : m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) = 0 -> exists g i, s_slots st2 !! (rid, 0) = Some (g, i) /\ m_sizeclass (MR st2 g) <= 23
                /\ (stdg (agt stA sc m (rid, 0) cnt AI) m = true -> m_sizeclass (MR st2 g) = bighost sc)).
  { rewrite MR', Emr. cbn [m_maplen]. intros Z0. exfalso. lia. }
  assert (SDc : stdg (agt stA sc m (rid, 0) cnt AI) m = true -> cnt = cmax sc).
  { unfold stdg, cls, cnt_of. rewrite MR', Emr. cbn -[Z.eqb Z.shiftr Z.mul Z.sub Z.add get_stride cmax S_ size_class agG m_set_maplen meta0].
    intros SD. apply andb_prop in SD as [SD1 _]. apply Z.eqb_eq in SD1. cbn in SD1. clear -SD1. lia. }
  assert (QGs : stdg (agt stA sc m (rid, 0) cnt AI) m = true -> (m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) = 0 <-> std_nested sc = true)
                /\ (m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) <> 0 -> m_maplen (MR (agt stA sc m (rid, 0) cnt AI) m) * 4096 = std_len sc)).
  { intros SD. destruct (STD (SDc SD)) as [EN SNF]. rewrite MR', Emr. cbn [m_maplen].
    split; [rewrite SNF; split; [intros; exfalso; lia| discriminate]| intros _; rewrite NEEDED; exact EN]. }
  assert (MS1 : s_metas st1' = s_metas st1 /\ s_groups st1' = s_groups st1).
  { unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); split; reflexivity. }
  assert (MS12 : s_metas st2 = s_metas st1 /\ s_groups st2 = s_groups st1) by exact MS1.
  assert (G12c : forall c, gcnt st2 c = gcnt st1 c).
  { intros c. destruct MS12 as [MS GS]. apply gcnt_frame; [exact GS|]. intros x _. unfold MR, get_meta_rec. rewrite MS. reflexivity. }
  pose proof (G12c sc) as G12.
  assert (QGsm : stdg (agt stA sc m (rid, 0) cnt AI) m = false -> gcnt st2 sc < 128).
  { intros SD. rewrite G12. apply NSTD. intros EC.
    unfold stdg, cls, cnt_of in SD. rewrite MR', Emr in SD. cbn -[Z.eqb Z.shiftr Z.mul Z.sub Z.add get_stride cmax S_ size_class agG m_set_maplen meta0] in SD.
    rewrite <- Emr, STRIDE in SD. replace (cnt - 1 =? 0) with false in SD by (symmetry; apply Z.eqb_neq; clear -EC CM; lia).
    replace (cnt - 1 + 1 =? cmax sc) with true in SD by (symmetry; apply Z.eqb_eq; clear -EC; lia). unfold S_ in SD. rewrite Z.eqb_refl in SD. discriminate. }
  destruct (agt_quant (xorph (X_as (m :: idle)) (Some rid)) (mkX idle [] None None (Some m)) st2 stA _ _ BL LS1 LS1 P sc m (rid, 0) cnt AI
              INV2 INV' eq_refl eq_refl LKm LKc HmA HmI HpN SG2 (QM_X (X_as (m :: idle)) (xorph (X_as (m :: idle)) (Some rid)) st2 0 eq_refl Q2) ltac:(intros x Hx; cbn in Hx |- *; destruct Hx as [Hx|Hx]; [left; symmetry; exact Hx| right; exact Hx]) A2 Hsc ROOM ltac:(lia) NEWG QGm QGn QGs QGsm)
    as (Qa & Qb & Qc).
  split; [split; [exact Qa|]; split; [exact (QM_X (mkX idle [] None None (Some m)) (X_as idle) _ 0 eq_refl Qb)| exact Qc]|].
  split.
  { intros c. rewrite (aq_gcnt (xorph (X_as (m :: idle)) (Some rid)) st2 stA _ BL LS1 sc m (rid, 0) cnt AI INV2 eq_refl LKm HmI HpN NEWG c).
    rewrite <- (G12c c). reflexivity. }

  eapply BLF_trans; [exact BF1|].
  assert (B12 : BLF st1 st2 BL).
  { intros kk _. unfold slotcls, cls, MR, get_meta_rec. rewrite (proj1 MS12). replace (s_slots st2) with (s_slots st1); [reflexivity|].
    unfold st2. change (s_slots (fst (new_region RKGroup a needed st1'))) with (s_slots st1').
    unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); reflexivity. }
  eapply BLF_trans; [exact B12|].
  apply (BLF_old _ st2 _ _ BL LS1 INV2).
  exact (aq_slotcls_old (xorph (X_as (m :: idle)) (Some rid)) (mkX idle [] None None (Some m)) st2 stA _ _ BL LS1 LS1 sc m (rid, 0) cnt AI
           INV2 INV' eq_refl LKm HmI HpN NEWG QGm QGn QGs QGsm).
Qed.

Theorem ag_mmap_fq :
  fqtree B L1 (SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
    if negb (mmap_answer_ok (live_ranges st1') needed r) then bad_answer bail
    else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
    else let '(st2, rid) := new_region RKGroup r needed st1' in
         ag_tail full_lay (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) sc m (rid, 0) cnt AI k)) Post.
Proof.
  destruct (st1'_facts idle st1 L1 BL LS1 m sc INV1 TF1) as (INV1' & SH1 & TK1 & ACT1 & TF1' & RG1 & SS1'). fold st1' in INV1', SH1, TK1, ACT1, TF1', RG1, SS1'.
  pose proof (grp_ok_sound sc cnt needed GRP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof QP1' as QP. destruct (QPOST_SINV P (m :: idle) BL st1' (X_as (m :: idle)) eq_refl QP) as [SI1' A1'].
  assert (MS1 : s_metas st1' = s_metas st1 /\ s_groups st1' = s_groups st1).
  { unfold st1', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); split; reflexivity. }
  apply fqtree_vis_map.
  -   cbn. left. split; [exact (brk_quiet_of _ _ _ (proj1 INV1'))|]. split; [reflexivity|]. split; [reflexivity|].
    split; [right; reflexivity|]. unfold LEN_MAX. lia.
  -
    intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha.
    change (event_post L1 (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L1 else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L1) L1 else KInv.set_groups ((a, needed) :: ld_groups L1) L1 else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L1)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha.
    destruct (is_err a) eqn:ER.
    + exact (state_bytes_B (X_as (m :: idle)) st1' L1 BL LS1 P B INV1' eq_refl eq_refl SI1' A1' HBP).
    + destruct (mmap_final a Ha ER) as (INVf & _ & _ & _ & _ & QPf & _ & _ & _).
      destruct (QPOST_SINV P idle BL _ (mkX idle [] None None (Some m)) eq_refl QPf) as [SIf Af].
      exact (state_bytes_B _ _ _ BL LS1 P B INVf eq_refl eq_refl SIf Af HBP).
  -
    left. pose proof (mmap_len_ge needed ltac:(lia)) as ML. unfold SMALLREQ. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [negb] in Ha |- *.
    change (event_post L1 (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L1 else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L1) L1 else KInv.set_groups ((a, needed) :: ld_groups L1) L1 else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L1)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. cbn [negb].
    destruct (is_err a) eqn:ER.
    +
      rewrite free_meta_eq.
      destruct (free_idle_ok idle m st1' L1 BL LS1 INV1' NIm) as (INV2 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
      eapply HK.
      * split; [intros sc' _; rewrite F7, ACT1; apply HA1|]. split; [exact HL1|].
        split.
        { eapply GP_trans; [exact HG1| apply GP_eq; [rewrite F5, RG1; reflexivity|]].
          unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st1')) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. cbn. exact SS1'. }
        split; [exact INV2|]. exact (TF0_ctrl st1' _ F1 F2 TF1').
      * exact (free_idle_q idle m st1' L1 BL LS1 P INV1' NIm QP).
      * intros c Hc. rewrite <- GLE1. apply Z.eq_le_incl. apply gcnt_frame; [rewrite F3; exact (proj2 MS1)|].
        intros x _. transitivity (geom (MR st1' x)); [| unfold MR, get_meta_rec; rewrite (proj1 MS1); reflexivity].
        apply geom_data. unfold fm_st. rewrite (fi_put idle m st1' L1 BL LS1 INV1'). apply queue_data.
      * eapply BLF_trans; [exact BF1|]. eapply BLF_trans; [| exact (BLF_free_idle idle m st1' L1 BL LS1 INV1')].
        apply BLF_qsame. eapply qsame_trans; [apply qsame_account_bounce| apply qsame_step_seq].
    +
      destruct (new_region RKGroup a needed st1') as [st2 rid] eqn:EN.
      assert (Erid : rid = s_next_rid st1') by (unfold new_region in EN; inversion EN; reflexivity).
      assert (Est2 : st2 = fst (new_region RKGroup a needed st1')) by (rewrite EN; reflexivity).
      destruct (mmap_final a Ha ER) as (INV' & TF' & MR' & GR' & ACT' & QPf & RGf & SSf & GCf & BFf). rewrite <- Est2, <- Erid in *.
      rewrite ag_tail_eq.
      change (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2)) with (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)).
      pose proof (top_facts rid sc cnt needed AI GRP Hsc) as TFX. cbn zeta in TFX.
      destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
      rewrite Emr in MR', F4, F5, F7, F8, F9. rewrite <- MR' in F4, F5, F7, F8, F9.
      eapply HK; [| exact QPf| intros c Hc; rewrite GCf, <- GLE1; destruct (Z.eqb_spec sc c); lia| exact BFf].
      split; [intros sc' _; apply ACT'|]. split; [cbn; exact HL1|].
      split.
      { eapply GP_trans; [exact HG1|]. split.
        - intros q rq Hq Kq. rewrite RGf, Est2. apply (ng_keep _ _ _ _ _ _ _ INV1'). rewrite RG1. exact Hq.
        - transitivity (s_secret st2); [rewrite agt_secret; reflexivity|]. rewrite SSf. reflexivity. }
      exists (rid, 0), AI, (cnt - 1), (Z.shiftr needed 12).
      pose proof (clamp_ai (UNIT * size_class sc) cnt ltac:(lia)) as HAI. cbn zeta in HAI. fold AI in HAI.
      split; [exact GR'|]. split; [exact MR'|]. split; [exact HAI|]. split; [lia|].
      assert (STR : get_stride (MR (agt (upd_meta m (m_set_maplen (Z.shiftr needed 12)) (upd_ctx MC st2)) sc m (rid, 0) cnt AI) m)
                    = if (cnt - 1 =? 0) && negb (Z.shiftr needed 12 =? 0) then Z.shiftr needed 12 * 4096 - UNIT else UNIT * size_class sc).
      { rewrite MR'. unfold get_stride. cbn. reflexivity. }
      assert (NZ : (Z.shiftr needed 12 =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite NZ in STR. cbn [negb] in STR. rewrite andb_true_r in STR.
      assert (E12 : Z.shiftr needed 12 * 4096 = needed) by (rewrite F10; apply round_up_pg_id; exact G2).
      split; [| split; [| split; [| split; [exact INV'| apply TF0_TF2; exact TF']]]].
      * destruct RED as [(C1 & Nd & S28)|NR].
        -- rewrite STR. replace (cnt - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite E12, Nd.
           pose proof (proj1 (round_up_pg_spec (req + IB + UNIT))). unfold UNIT, IB in *. lia.
        -- rewrite STR. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|C1]; [| lia]. rewrite E12. assert (C1' : cnt = 1) by lia. rewrite C1', Z.mul_1_r in NR. unfold UNIT, IB in *. lia.
      * intros S28. destruct RED as [(C1 & Nd & S28')|NR]; [lia|].
        rewrite STR in F5 |- *. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| reflexivity].
        destruct F5 as [F5|]; [| lia]. rewrite E12 in F5 |- *. assert (cnt = 1) by lia. subst cnt. lia.
      * intros UNDER. rewrite STR in UNDER. destruct RED as [(C1 & Nd & S28)|NR].
        -- clear - HAI C1. lia.
        -- exfalso. destruct (Z.eqb_spec (cnt - 1) 0) as [C1|]; [| lia]. rewrite E12 in UNDER. assert (cnt = 1) by lia. subst cnt. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV1')) in Ha. rewrite Ha. exact I.
Qed.
End MMAP_BRANCHQ.

Definition REC_OKQ (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (P : Z -> Z) (B : Z) (Post : mled -> T -> Prop) : Prop :=
  forall j idle st L BL LS req (k : mstate -> Z -> M T) bail,
  sc < j < 48 ->
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= req -> req + IB <= UNIT * size_class j ->
  QPOST P idle BL st -> zlen idle <= rank j -> PHI P + R63 BL <= B + 3 * PGSZ ->
  (forall st1 idx L1 LS1, SLOT_POST idle j req st L BL st1 idx L1 LS1 -> QPOST P idle BL st1 ->
     (forall c, 0 <= c < j -> gcnt st1 c <= gcnt st c) -> BLF st st1 BL -> fqtree B L1 (k st1 idx) Post) ->
  fqtree B L (rec st j req k bail) Post.

Section NEST_BRANCHQ.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T).
Variables (idle : list aptr) (st0 st1 : mstate) (L0 L1 : mled) (BL : list blk) (LS1 : lhead -> list aptr) (P : Z -> Z) (B : Z).
Variables (m : aptr) (sc req cnt : Z) (k : mstate -> optr -> M T) (bail : M T) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OKQ T rec sc P B Post.
Hypothesis INV1 : INVL (X_as (m :: idle)) st1 L1 BL LS1.
Hypothesis NIm : ~ In m idle.
Hypothesis ND : NoDup idle.
Hypothesis TF1 : TF0 st1.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hreq : 0 <= req.
Hypothesis Hfit : req + IB <= UNIT * size_class sc.
Hypothesis HA1 : forall sc', active st1 sc' = active st0 sc'.
Hypothesis HA0 : active st0 sc = None.
Hypothesis HL1 : ld_live L1 = ld_live L0.
Hypothesis HG1 : GP st0 st1.
Hypothesis NEST : nest_ok sc cnt = true.
Hypothesis QP1 : QPOST P (m :: idle) BL st1.
Hypothesis NSTD : cnt <> cmax sc -> gcnt st1 sc < 128.
Hypothesis GLE1 : forall c, gcnt st1 c = gcnt st0 c.
Hypothesis BF1 : BLF st0 st1 BL.
Hypothesis RK : zlen idle + 1 <= rank (size_to_class (UNIT + cnt * (UNIT * size_class sc) - IB)).
Hypothesis HBP : PHI P + R63 BL <= B + 3 * PGSZ.
Hypothesis HK : AGK T P B Post idle sc req st0 L0 BL k.
Let size := UNIT * size_class sc.
Let j := size_to_class (UNIT + cnt * size - IB).

Theorem ag_nest_fq :
  fqtree B L1 (rec st1 j (UNIT + cnt * size - IB) (fun st2 idx =>
     if idx <? 0 then free_meta m st2 (fun st3 => k st3 None) bail
     else match active st2 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g => ag_tail full_lay (upd_meta m (m_set_maplen 0) (nest_layout st2 g idx j size cnt)) sc m (slot_of st2 g idx) cnt (cnt - 1) k
          end) bail) Post.
Proof.
  pose proof (nest_ok_sound sc cnt NEST) as N0. cbn zeta in N0. fold size in N0. fold j in N0. destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
  apply (REC j (m :: idle) st1 L1 BL LS1 (UNIT + cnt * size - IB) _ bail ltac:(lia) INV1 TF1).
  - apply NoDup_cons_2; [intros Hin; apply NIm; apply (proj1 (list_elem_of_In _ _)); exact Hin| exact ND].
  - exact N5.
  - lia.
  - exact QP1.
  - rewrite zlen_cons. fold size in RK. fold j in RK. lia.
  - exact HBP.
  - intros st2 idx L2 LS2 (ACT & LIVE & GP2 & RES) QP2 GLE2 BF2.
    destruct RES as [(-> & INV2 & TF2')|(g & bg & aig & Hidx & HAj & Hg & SCg & FIT & STR & INV2 & TF2')].
    +
      change (-1 <? 0) with true. cbn iota. rewrite free_meta_eq.
      destruct (free_idle_ok idle m st2 L2 BL LS2 INV2 NIm) as (INV3 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
      eapply HK.
      * split; [intros sc' Hs; rewrite F7, ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
        split.
        { eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq; [exact F5|]]].
          unfold fm_st. destruct (queue_frame LFree m (put_meta m meta0 st2)) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. reflexivity. }
        split; [exact INV3|]. exact (TF0_ctrl st2 _ F1 F2 TF2').
      * exact (free_idle_q idle m st2 L2 BL LS2 P INV2 NIm QP2).
      * intros c Hc. rewrite <- GLE1. etransitivity; [| apply (GLE2 c); lia]. apply Z.eq_le_incl. apply gcnt_frame; [exact F3|].
        intros x _. apply geom_data. unfold fm_st. rewrite (fi_put idle m st2 L2 BL LS2 INV2). apply queue_data.
      * eapply BLF_trans; [exact BF1|]. eapply BLF_trans; [exact BF2| exact (BLF_free_idle idle m st2 L2 BL LS2 INV2)].
    + replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HAj.
      assert (Hgh : hosts st2 bg g) by (exists aig; exact Hg).
      assert (Ep : slot_of st2 g idx = (fst bg, sstart (MR st2 g) idx)).
      { unfold slot_of. fold (MR st2 g). exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV2))) _ _ idx Hgh). }
      rewrite Ep. rewrite ag_tail_eq.
      specialize (STR ltac:(lia)).
      assert (EMP : LS2 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV2); rewrite ACT by lia; rewrite HA1; exact HA0).
      destruct (ag_nested_ok idle st2 L2 BL LS2 m g bg aig idx sc cnt INV2 Hg Hidx SCg STR NEST Hsc EMP TF2' NIm)
        as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
      pose proof (nst_facts st2 g bg idx sc cnt NEST Hsc) as NF. cbn zeta in NF.
      destruct NF as (_ & _ & _ & _ & _ & _ & _ & Emr & Es).
      fold size in MR', GR', ACT', INV', TF', Emr, Es |- *. fold j in MR', GR', ACT', INV', TF' |- *.
      rewrite Emr in MR'. rewrite Emr in Es.

      set (p := (fst bg, sstart (MR st2 g) idx)) in *.
      set (stA := upd_meta m (m_set_maplen 0) (nest_layout st2 g idx j size cnt)) in *.
      pose proof (strip_nest_layout st2 g idx j size cnt) as SN.
      assert (LKg : s_groups stA = s_groups st2) by (unfold stA; rewrite s_groups_upd_meta || cbn; transitivity (s_groups (strip (nest_layout st2 g idx j size cnt))); [reflexivity|]; rewrite SN; reflexivity).
      assert (LKr : s_regions stA = s_regions st2) by (unfold stA; transitivity (s_regions (strip (nest_layout st2 g idx j size cnt))); [reflexivity|]; rewrite SN; reflexivity).
      assert (MSn : s_metas (nest_layout st2 g idx j size cnt) = s_metas st2) by (transitivity (s_metas (strip (nest_layout st2 g idx j size cnt))); [reflexivity|]; rewrite SN; reflexivity).
      assert (CXn : s_ctx (nest_layout st2 g idx j size cnt) = s_ctx st2) by (transitivity (s_ctx (strip (nest_layout st2 g idx j size cnt))); [reflexivity|]; rewrite SN; reflexivity).
      assert (LKm : forall x, x <> m -> s_metas stA !! x = s_metas st2 !! x) by (intros x NE; unfold stA; rewrite s_metas_upd_meta, lookup_insert_ne by congruence; exact (f_equal (fun t => t !! x) MSn) || (rewrite MSn; reflexivity)).
      assert (LKc : c_avail_meta_count (s_ctx stA) = c_avail_meta_count (s_ctx st2) /\ c_avail_meta_areas (s_ctx stA) = c_avail_meta_areas (s_ctx st2)
                    /\ c_meta_alloc_shift (s_ctx stA) = c_meta_alloc_shift (s_ctx st2)) by (unfold stA; rewrite s_ctx_upd_meta || cbn -[nest_layout]; rewrite CXn; repeat split; reflexivity).
      assert (HmA : s_metas stA !! m <> None) by (unfold stA; rewrite s_metas_upd_meta, lookup_insert_eq; discriminate).
      pose proof INV2 as (IR2 & IA2 & IM2 & IL2 & IG2 & IS2 & ISH2).
      assert (HmI : s_metas st2 !! m = Some meta0) by exact (proj1 (im_idle _ _ _ IM2 m ltac:(left; reflexivity))).
      assert (Ep' : p = slot_start' (MR st2 g) idx) by (unfold p; symmetry; exact (slot_start'_eq _ _ _ IM2 _ _ idx Hgh)).
      assert (HpN : s_groups st2 !! p = None).
      { pose proof (is_part _ _ _ IS2 bg g aig idx Hg Hidx) as P5. cbn zeta in P5. rewrite <- Ep' in P5.
        destruct P5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDE).
        destruct (s_groups st2 !! p) as [h|] eqn:E; [| reflexivity]. exfalso. apply NDE. split; [rewrite E; discriminate| reflexivity]. }
      assert (HsP : s_slots st2 !! p = Some (g, idx)) by (rewrite Ep'; exact (is_total _ _ _ IS2 bg g idx Hgh Hidx)).
      destruct QP2 as (SG2 & Q2 & A2).
      assert (ROOM : gcnt st2 sc <= CAP P sc) by (apply (creation_room _ st2 _ BL LS2 P INV2 SG2 A2 sc Hsc eq_refl); rewrite ACT by lia; rewrite HA1; exact HA0).
      assert (NEWG : m_sizeclass (MR (agt stA sc m p cnt (cnt - 1)) m) = sc /\ m_last_idx (MR (agt stA sc m p cnt (cnt - 1)) m) = cnt - 1) by (rewrite MR'; split; reflexivity).
      assert (SDc : stdg (agt stA sc m p cnt (cnt - 1)) m = (cnt =? cmax sc)).
      { unfold stdg, cls, cnt_of. rewrite MR'. cbn -[Z.eqb Z.mul Z.sub Z.add get_stride cmax S_ size_class]. rewrite Es. unfold size, S_. rewrite Z.eqb_refl, andb_true_r.
        replace (cnt - 1 + 1) with cnt by lia. reflexivity. }
      assert (BH : cnt = cmax sc -> std_nested sc = true /\ bighost sc = j).
      { intros EC. assert (SN2 : std_nested sc = true).
        { unfold std_nested, std_span, S_. apply Z.leb_le. rewrite <- EC. fold size.
          unfold UNIT, IB, PGSZ in N6 |- *. clear -N6. lia. }
        split; [exact SN2|]. unfold bighost. rewrite SN2. unfold std_span, S_, j. rewrite <- EC. fold size. f_equal. unfold UNIT. lia. }
      assert (QGm : m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) <> 0 -> m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) * 4096 <= cnt * S_ sc + 4111 /\ s_slots st2 !! p = None).
      { rewrite MR'. cbn [m_maplen]. intros Z0. exfalso. exact (Z0 eq_refl). }
      assert (QGn : m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) = 0 -> exists g0 i0, s_slots st2 !! p = Some (g0, i0) /\ m_sizeclass (MR st2 g0) <= 23
                    /\ (stdg (agt stA sc m p cnt (cnt - 1)) m = true -> m_sizeclass (MR st2 g0) = bighost sc)).
      { intros _. exists g, idx. split; [exact HsP|]. rewrite SCg. split; [lia|]. rewrite SDc. intros EC. apply Z.eqb_eq in EC. destruct (BH EC) as [_ E]. symmetry. exact E. }
      assert (QGs : stdg (agt stA sc m p cnt (cnt - 1)) m = true -> (m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) = 0 <-> std_nested sc = true)
                    /\ (m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) <> 0 -> m_maplen (MR (agt stA sc m p cnt (cnt - 1)) m) * 4096 = std_len sc)).
      { rewrite SDc. intros EC. apply Z.eqb_eq in EC. destruct (BH EC) as [SN2 _]. rewrite MR'. cbn [m_maplen]. rewrite SN2. split; [split; intros; reflexivity| intros Z0; exfalso; exact (Z0 eq_refl)]. }
      assert (QGsm : stdg (agt stA sc m p cnt (cnt - 1)) m = false -> gcnt st2 sc < 128).
      { rewrite SDc. intros EC. apply Z.eqb_neq in EC. pose proof (GLE2 sc ltac:(lia)). pose proof (NSTD EC). lia. }
      destruct (agt_quant (xpend (X_as (m :: idle)) (Some p)) (mkX idle [] None None (Some m)) st2 stA _ _ BL LS2 LS2 P sc m p cnt (cnt - 1)
                  INV2 INV' LKg LKr LKm LKc HmA HmI HpN SG2 (QM_X (X_as (m :: idle)) (xpend (X_as (m :: idle)) (Some p)) st2 0 eq_refl Q2)
                  ltac:(intros x Hx; cbn in Hx |- *; destruct Hx as [Hx|Hx]; [left; symmetry; exact Hx| right; exact Hx]) A2 Hsc ROOM ltac:(lia) NEWG QGm QGn QGs QGsm)
        as (Qa & Qb & Qc).
      eapply HK.
      * split; [intros sc' Hs; rewrite ACT', ACT by lia; apply HA1|]. split; [rewrite LIVE; exact HL1|].
        split.
        { eapply GP_trans; [exact HG1| eapply GP_trans; [exact GP2| apply GP_eq]].
          - rewrite agt_regions. exact LKr.
          - rewrite agt_secret. change (s_secret (nest_layout st2 g idx j size cnt) = s_secret st2).
            rewrite <- (s_secret_strip (nest_layout st2 g idx j size cnt)), SN. reflexivity. }
        exists p, (cnt - 1), (cnt - 1), 0.
        rewrite Z.sub_diag. split; [exact GR'|]. split; [exact MR'|]. split; [lia|]. split; [lia|].
        rewrite MR', Es. split; [unfold size; lia|]. split; [intros _; reflexivity|]. split; [unfold size; intros; lia|].
        split; [exact INV'| exact TF'].
      * split; [exact Qa|]. split; [exact (QM_X (mkX idle [] None None (Some m)) (X_as idle) _ 0 eq_refl Qb)| exact Qc].
      * intros c Hc. rewrite (aq_gcnt (xpend (X_as (m :: idle)) (Some p)) st2 stA _ BL LS2 sc m p cnt (cnt - 1) INV2 LKg LKm HmI HpN NEWG c).
        replace (sc =? c) with false by (symmetry; apply Z.eqb_neq; lia). rewrite <- GLE1. pose proof (GLE2 c ltac:(lia)). lia.
      * eapply BLF_trans; [exact BF1|]. eapply BLF_trans; [exact BF2|].
        apply (BLF_old _ st2 _ _ BL LS2 INV2).
        exact (aq_slotcls_old (xpend (X_as (m :: idle)) (Some p)) (mkX idle [] None None (Some m)) st2 stA _ _ BL LS2 LS2 sc m p cnt (cnt - 1)
                 INV2 INV' LKg LKm HmI HpN NEWG QGm QGn QGs QGsm).
Qed.
End NEST_BRANCHQ.

Lemma ag_cnt1_ge128 sc u0 : 0 <= sc < 48 -> 128 <= u0 -> ag_cnt1 sc u0 = cmax sc.
Proof.
  intros Hsc Hu. unfold ag_cnt1. rewrite (cnt0_of_ge128 sc u0 Hsc Hu). pose proof (tab_basic_ok sc Hsc) as (_ & CM & _).
  replace (cmax sc =? 1) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma ag_cnt1_nstd sc u0 : 0 <= sc < 48 -> ag_cnt1 sc u0 <> cmax sc -> u0 < 128.
Proof. intros Hsc H. destruct (Z.lt_ge_cases u0 128) as [L|G]; [exact L|]. exfalso. apply H. apply ag_cnt1_ge128; assumption. Qed.

Definition cnt0_range_f (sc : Z) : bool := forallb (fun c => (1 <=? c) && (c <=? 32)) (cnt0_list sc).
Lemma cnt0_range_all : forallb cnt0_range_f classes = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cnt0_range sc c : 0 <= sc < 48 -> In c (cnt0_list sc) -> 1 <= c <= 32.
Proof.
  intros Hsc Hc. pose proof (forallb_classes _ cnt0_range_all sc Hsc) as T. unfold cnt0_range_f in T. rewrite forallb_forall in T.
  specialize (T c Hc). apply andb_prop in T as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.
Lemma ag_cnt1_range sc u0 : 0 <= sc < 48 -> 1 <= ag_cnt1 sc u0 <= 32.
Proof.
  intros Hsc. unfold ag_cnt1. pose proof (cnt0_range sc _ Hsc (cnt0_in sc u0)) as R.
  destruct (_ && _) eqn:E; [apply andb_prop in E as [E _]; apply Z.eqb_eq in E; lia| exact R].
Qed.

Lemma ag_cnt_facts sc req u0 u1 ns c3 n3 :
  0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc -> u0 <= u1 ->
  PGSZ / 2 < UNIT * size_class sc * ag_cnt1 sc u0 + UNIT ->
  ag_cn3 sc req (ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) u1 ns = (c3, n3) ->
  (c3 = cmax sc -> n3 = std_len sc /\ std_nested sc = false) /\ (c3 <> cmax sc -> u0 < 128) /\ n3 <= UNIT * size_class sc * c3 + 4111.
Proof.
  intros Hsc Hreq Hfit HU HB E. pose proof (tab_basic_ok sc Hsc) as (S16 & CM & _).
  set (c1 := ag_cnt1 sc u0) in *.
  assert (C2 : ag_cnt2 sc c1 u1 ns = c1 \/ (ag_cnt2 sc c1 u1 ns <= 5 /\ u1 < 4 * c1)).
  { unfold ag_cnt2. destruct (Z.ltb_spec u1 (4 * c1)); cbn [andb]; [| left; reflexivity]. destruct ns; cbn; [left; reflexivity|].
    destruct (adj_small sc (UNIT * size_class sc) c1) as [E1|LE]; [left; exact E1| right; split; [exact LE| assumption]]. }
  set (c2 := ag_cnt2 sc c1 u1 ns) in *.
  assert (C1R : c1 = cmax sc \/ u0 < 128) by (destruct (Z.eq_dec c1 (cmax sc)); [left; assumption| right; apply (ag_cnt1_nstd sc u0 Hsc); assumption]).
  assert (C1B : 1 <= c1 <= 32) by (unfold c1; apply ag_cnt1_range; exact Hsc).
  unfold ag_cn3 in E. cbn zeta in E.
  assert (RU : forall x, x <= round_up_pg x <= x + 4095) by (intros x; pose proof (round_up_pg_spec x); lia).
  destruct (negb ns && (c2 <=? 7)) eqn:E7.
  - destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
    + inversion E; subst c3 n3. split; [intros E1; exfalso; lia|]. split.
      * intros _. apply andb_prop in E7 as [_ E7]. apply Z.leb_le in E7. destruct C2 as [E2|[LE LT]]; [| lia]. destruct C1R as [E1|L]; [| exact L]. exfalso. unfold c2 in E7. lia.
      * pose proof (RU (req + IB + UNIT)). unfold IB, UNIT in *. lia.
    + inversion E; subst c3 n3. apply andb_prop in E7 as [_ E7]. apply Z.leb_le in E7. split; [intros E1; exfalso; lia|]. split.
      * intros _. destruct C2 as [E2|[LE LT]]; [| lia]. destruct C1R as [E1|L]; [| exact L]. exfalso. unfold c2 in E7. lia.
      * pose proof (RU (UNIT * size_class sc * c2 + UNIT)). unfold UNIT in *. lia.
  - inversion E; subst c3 n3. split; [| split].
    + intros E2. assert (E1 : c1 = cmax sc) by (destruct C2 as [E0|[LE LT]]; lia).
      split; [unfold std_len, std_span, S_; rewrite E2; f_equal; lia|].
      unfold std_nested, std_span, S_. apply Z.leb_gt. rewrite <- E1. unfold c1 in HB |- *. lia.
    + intros NE. destruct C2 as [E0|[LE LT]]; [destruct C1R as [E1|L]; [exfalso; apply NE; lia| exact L]| lia].
    + pose proof (RU (UNIT * size_class sc * c2 + UNIT)). unfold UNIT in *. lia.
Qed.

Lemma gcnt_nonneg X st L BL LS c : INVL X st L BL LS -> 0 <= gcnt st c.
Proof.
  intros INV. rewrite gcnt_gmetas. apply zsum_map_nonneg. intros [m b] Hin. cbn. destruct (gfacts X st L BL LS INV m b Hin) as ([? ?] & _).
  destruct (_ =? _); lia.
Qed.

Section AGQ.
Variables (T : Type) (rec : mstate -> Z -> Z -> (mstate -> Z -> M T) -> M T -> M T) (sc : Z) (P : Z -> Z) (B : Z) (Post : mled -> T -> Prop).
Hypothesis REC : REC_OKQ T rec sc P B Post.

Theorem alloc_group_fq idle st L BL LS req (k : mstate -> optr -> M T) bail :
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  active st sc = None -> QPOST P idle BL st -> zlen idle <= rank sc -> PHI P + R63 BL <= B + 3 * PGSZ ->
  AGK T P B Post idle sc req st L BL k ->
  fqtree B L (alloc_group T full_lay rec st sc req k bail) Post.
Proof.
  intros INV TF ND Hsc Hreq Hfit HA QP RK HBP HK. pose proof QP as (SGst & Qst & Ast). unfold alloc_group.
  destruct (QPOST_SINV P idle BL st (X_as idle) eq_refl QP) as [SIst _].
  pose proof (rank_range sc) as RR.
  eapply (alloc_meta_fq T BL P B Post _ bail (X_as idle) st L LS INV SGst Ast); [ | | | | exact INV| apply amf_refl| apply lf_refl| | reflexivity].
  -
    intros HFH. pose proof (ncarved_le_groups (X_as idle) st L BL LS INV 0 Qst HFH eq_refl) as NC.
    pose proof (ngroups_le (X_as idle) st L BL LS P INV SGst Ast) as NG0. cbn [x_idle X_as] in NC. unfold NCAP. lia.
  -
    exact (group_bytes_B (X_as idle) st L BL LS P B INV eq_refl eq_refl SIst Ast HBP).
  -
    intros st1 L1 LS1 INV1 AF LF SI1 A1 GC1 GEO1. cbn beta iota. eapply HK.
    + split; [intros sc' _; apply (amf_active _ _ AF)|]. split; [exact (lf_live _ _ LF)|]. split; [exact (GP_amf _ _ AF)|]. split; [exact INV1|].
      exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
    + exact (SINV_QPOST P idle BL st1 (X_as idle) eq_refl SI1 A1).
    + intros c Hc. rewrite GC1. lia.
    + exact (BLF_geo _ st st1 L BL LS INV (amf_slots _ _ AF) GEO1).
  -
    intros st1 L1 LS1 m INV1 NIm AF LF SI1 A1 NC1 GC1 GEO1. cbn beta iota zeta.
    pose proof (BLF_geo _ st st1 L BL LS INV (amf_slots _ _ AF) GEO1) as BF1. cbn [xidle X_as x_idle x_zomb x_pend x_orph x_fresh] in INV1, NIm, SI1. change (mkX (m :: idle) [] None None None) with (X_as (m :: idle)) in INV1, SI1.
    change (if sc <? 9 then small_cnt_pick sc (usage st1 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) (UNIT * size_class sc))
      with (cnt0_of sc (usage st1 sc)).
    change (if (cnt0_of sc (usage st1 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage st1 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage st1 sc))
      with (ag_cnt1 sc (usage st1 sc)).
    change (lh_nest full_lay) with nest_layout.
    assert (HA1 : forall sc', active st1 sc' = active st sc') by (intros; apply (amf_active _ _ AF)).
    assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF).
    pose proof (SINV_QPOST P (m :: idle) BL st1 (X_as (m :: idle)) eq_refl SI1 A1) as QP1.
    assert (U0 : usage st1 sc = gcnt st1 sc) by exact (ia_usage _ (proj1 (proj2 INV1)) sc Hsc).
    pose proof (ag_arith sc req (usage st1 sc)) as AR.
    set (c1 := ag_cnt1 sc (usage st1 sc)) in *.
    destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1 + UNIT)) as [HB|HB].
    +
      set (ns := is_bouncing sc st1).
      set (st1' := step_seq (account_bounce sc st1)).
      set (u1 := if Z.even sc && (sc <? 32) then usage st1 sc + usage st1' (sc + 1) else usage st1 sc).
      change (if (u1 <? 4 * c1) && negb ns
              then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * c1) then 2
                   else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * c1) then 3
                   else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * c1) then 5
                   else c1
              else c1) with (ag_cnt2 sc c1 u1 ns).
      set (c2 := ag_cnt2 sc c1 u1 ns).
      specialize (AR u1 ns).
      assert (HU : usage st1 sc <= u1).
      { unfold u1. destruct (Z.even sc && (sc <? 32)) eqn:E; [| lia].
        apply andb_prop in E as [_ E]. apply Z.ltb_lt in E.
        destruct (st1'_facts idle st1 L1 BL LS1 m sc INV1 TF1) as (INV1' & _). fold st1' in INV1'.
        rewrite (ia_usage _ (proj1 (proj2 INV1')) (sc + 1) ltac:(lia)). pose proof (gcnt_nonneg _ _ _ _ _ (sc + 1) INV1'). lia. }
      assert (GO : forall c3 n3, ag_cn3 sc req c2 u1 ns = (c3, n3) ->
        fqtree B L1 (SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
          if negb (mmap_answer_ok (live_ranges st1') n3 r) then bad_answer bail
          else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
          else let '(st2, rid) := new_region RKGroup r n3 st1' in
               ag_tail full_lay (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st2)) sc m (rid, 0) c3
                 (let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai) k)) Post).
      { intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hsc Hreq Hfit) HB E3) as [GRP RED].
        destruct (ag_cnt_facts sc req (usage st1 sc) u1 ns c3 n3 Hsc Hreq Hfit HU HB E3) as (STD & NSTD & NUB).
        apply (ag_mmap_fq T idle st st1 L L1 BL LS1 P B m sc req c3 n3 k bail Post INV1 NIm TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) GRP RED QP1 STD); [| exact NUB| exact GC1| exact BF1| exact HBP| exact HK].
        intros NE. rewrite <- U0. exact (NSTD NE). }
      unfold ag_cn3 in GO. cbn zeta in GO.
      destruct (negb ns && (c2 <=? 7)).
      * destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
        -- cbn beta iota. exact (GO _ _ eq_refl).
        -- cbn beta iota. exact (GO _ _ eq_refl).
      * cbn beta iota. exact (GO _ _ eq_refl).
    +
      pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST.
      apply (ag_nest_fq T rec idle st st1 L L1 BL LS1 P B m sc req c1 k bail Post REC INV1 NIm ND TF1 Hsc Hfit HA1 HA (lf_live _ _ LF) (GP_amf _ _ AF) NEST QP1); [| exact GC1| exact BF1| | exact HBP| exact HK].
      * intros NE. rewrite <- U0. apply (ag_cnt1_nstd sc); [exact Hsc| exact NE].
      * pose proof (nest_host sc (usage st1 sc) Hsc) as NH. cbn zeta in NH.
        change (bump (UNIT * size_class sc) (cnt0_of sc (usage st1 sc))) with c1 in NH.
        specialize (NH HB).
        pose proof (nest_ok_sound sc c1 NEST) as N0. cbn zeta in N0. destruct N0 as (_ & N2 & _).
        pose proof (rank_host sc (size_to_class (UNIT + c1 * (UNIT * size_class sc) - IB)) ltac:(lia) NH). lia.
  -   split; [exact Qst|]. split; [reflexivity|]. split; [reflexivity|]. intros x _. reflexivity.
Qed.
End AGQ.

Section SLOTQ.
Variables (T : Type) (P : Z -> Z) (B : Z) (Post : mled -> T -> Prop).

Theorem alloc_slot_fq (f : nat) : forall sc idle st L BL LS req (k : mstate -> Z -> M T) bail,
  49 - sc <= Z.of_nat f ->
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  QPOST P idle BL st -> zlen idle <= rank sc -> PHI P + R63 BL <= B + 3 * PGSZ ->
  (forall st1 idx L1 LS1, SLOT_POST idle sc req st L BL st1 idx L1 LS1 -> QPOST P idle BL st1 ->
     (forall c, 0 <= c < sc -> gcnt st1 c <= gcnt st c) -> BLF st st1 BL -> fqtree B L1 (k st1 idx) Post) ->
  fqtree B L (alloc_slot full_lay f st sc req k bail) Post.
Proof.
  induction f as [|f IH]; intros sc idle st L BL LS req k bail Hf INV TF ND Hsc Hreq Hfit QP RK HBP HK.
  { exfalso. cbn in Hf. lia. }
  change (alloc_slot full_lay (S f) st sc req k bail) with
    (try_avail sc st (fun st1 first =>
       if negb (first =? 0) then k st1 (ctz32 first)
       else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
              match go with
              | None => k st2 (-1)
              | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                          queue (LActive sc) g st3 (fun st4 => k st4 0) bail
              end) bail) bail).
  destruct (try_avail_okQ T (X_as idle) L BL sc
              (fun st1 first =>
                 if negb (first =? 0) then k st1 (ctz32 first)
                 else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
                        match go with
                        | None => k st2 (-1)
                        | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                                    queue (LActive sc) g st3 (fun st4 => k st4 0) bail
                        end) bail) bail eq_refl eq_refl Hsc st LS INV) as (st1 & first & LS1 & E & [TAF RES] & FF).
  rewrite E. cbn beta.
  assert (ACT1 : forall sc', sc' < sc -> active st1 sc' = active st sc').
  { intros sc' Hs. change (active st1 sc') with (get_head st1 (LActive sc')). rewrite (taf_heads _ _ _ TAF) by (intros EQ; inversion EQ; lia). reflexivity. }
  assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (taf_shadow _ _ _ TAF) (taf_tick _ _ _ TAF) TF).

  pose proof QP as (SGst & Qst & Ast). destruct (QPOST_SINV P idle BL st (X_as idle) eq_refl QP) as [SIst _].
  assert (XFER : forall X1, x_idle X1 = idle -> INVL X1 st1 L BL LS1 -> QPOST P idle BL st1 /\ (forall c, 0 <= c < 48 -> gcnt st1 c <= gcnt st c) /\ BLF st st1 BL).
  { intros X1 HX INV1.
    destruct (SINVx_xfer (X_as idle) X1 st st1 L L BL LS LS1 P None INV INV1 ltac:(rewrite HX; reflexivity) FF Ast (SINV_SINVx _ _ _ SIst) ltac:(intros; discriminate)) as (SI1 & A1 & GC & _).
    split; [exact (SINV_QPOST P idle BL st1 X1 HX SI1 A1)|]. split; [exact GC| exact (BLF_ffr X1 st st1 L BL LS1 INV1 FF)]. }
  destruct RES as [(-> & HA & INV1)|(g & bg & ai & idx & NZ & POS & Eidx & HA & Hg & Hidx & SC & STR & INV1)].
  -
    change (negb (0 =? 0)) with false. cbn iota.
    destruct (XFER (X_as idle) eq_refl INV1) as (QP1 & GC1 & BF1).
    assert (RECQ : REC_OKQ T (alloc_slot full_lay f) sc P B Post).
    { intros j idle' st' L' BL' LS' req' k' bail' Hj INV' TF' ND' Hreq' Hfit' QP' RK' HBP' HK'.
      apply (IH j idle' st' L' BL' LS' req' k' bail'); try assumption; lia. }
    apply (alloc_group_fq T (alloc_slot full_lay f) sc P B Post RECQ idle st1 L BL LS1 req _ bail INV1 TF1 ND Hsc Hreq Hfit HA QP1 RK HBP).
    intros st2 go L2 LS2 (ACT2 & LIVE2 & GP2 & RES2) QP2 GLE2 BF2. destruct go as [g|].
    + destruct RES2 as (b & ai & last & ml & Hb & Em & Hai & Hl & FIT & STR & UND & INV2 & TF2').
      cbn zeta.
      destruct (slot_finish_ok T idle st2 L2 BL LS2 g b ai last sc ml (fun st4 => k st4 0) bail INV2 Hb Em Hai Hl Hsc
                  ltac:(rewrite ACT2 by lia; exact HA) UND TF2')
        as (LS4 & EQ & INV4 & TF4 & HA4 & ACT4 & G4 & TK4 & SH4 & L4 & SC4 & STR4 & SS4 & RG4 & SE4).
      rewrite EQ.

      set (st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2) in *.
      set (st4 := queue_st (LActive sc) g st3) in *.
      assert (F24 : FFR st2 st4).
      { apply (FFR_trans st2 st3 st4).
        - unfold st3. apply FFR_upd_meta; [exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV2))))) _ _ _ Hb))| intros r; destruct r; reflexivity| intros r Hr; destruct r; exact Hr].
        - unfold st4. apply FFR_queue_st.
          + unfold st3. rewrite s_metas_upd_meta, lookup_insert_eq. discriminate.
          + unfold st3, MR. rewrite get_meta_rec_upd_same. fold (MR st2 g). rewrite Em. cbn. discriminate.
          + intros a Ha. exfalso. unfold st3 in Ha. rewrite get_head_upd_meta in Ha. cbn in Ha. rewrite ACT2 in Ha by lia. rewrite HA in Ha. discriminate.
          + intros a z Ha. exfalso. unfold st3 in Ha. rewrite get_head_upd_meta in Ha. cbn in Ha. rewrite ACT2 in Ha by lia. rewrite HA in Ha. discriminate. }
      destruct QP2 as (SG2 & Q2 & A2). destruct (QPOST_SINV P idle BL st2 (mkX idle [] None None (Some g)) eq_refl (conj SG2 (conj Q2 A2))) as [SI2 _].
      destruct (SINVx_xfer (mkX idle [] None None (Some g)) _ st2 st4 L2 L2 BL LS2 LS4 P None INV2 INV4 eq_refl F24 A2 (SINV_SINVx _ _ _ SI2) ltac:(intros; discriminate)) as (SI4 & A4 & GC4 & _).
      eapply HK.
      * split; [intros sc' Hs; rewrite ACT4, ACT2 by lia; apply ACT1; exact Hs|]. split; [exact LIVE2|].
        split; [eapply GP_trans; [exact (GP_taf _ _ _ TAF)| eapply GP_trans; [exact GP2| apply GP_eq; [exact RG4| exact SE4]]]|].
        right. exists g, b, ai. rewrite L4, SC4, STR4, G4, SS4.
        split; [lia|]. split; [exact HA4|]. split; [exact Hb|]. split; [reflexivity|]. split; [exact FIT|]. split; [exact STR|].
        split; [exact INV4| exact TF4].
      * exact (SINV_QPOST P idle BL st4 (xpend (X_as idle) (Some (fst b, sstart (MR st2 g) 0))) eq_refl SI4 A4).
      * intros c Hc. pose proof (GC4 c ltac:(lia)). pose proof (GLE2 c Hc). pose proof (GC1 c ltac:(lia)). lia.
      * eapply BLF_trans; [exact BF1|]. eapply BLF_trans; [exact BF2|]. exact (BLF_ffr _ st2 st4 L2 BL LS4 INV4 F24).
    + destruct RES2 as [INV2 TF2']. eapply HK.
      * split; [intros sc' Hs; rewrite ACT2 by lia; apply ACT1; exact Hs|]. split; [exact LIVE2|].
        split; [eapply GP_trans; [exact (GP_taf _ _ _ TAF)| exact GP2]|].
        left. split; [reflexivity|]. split; [exact INV2| exact TF2'].
      * exact QP2.
      * intros c Hc. pose proof (GLE2 c Hc). pose proof (GC1 c ltac:(lia)). lia.
      * eapply BLF_trans; [exact BF1| exact BF2].
  -
    replace (negb (first =? 0)) with true by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact NZ).
    cbn iota. rewrite Eidx.
    destruct (XFER (xpend (X_as idle) (Some (fst bg, sstart (MR st1 g) idx))) eq_refl INV1) as (QP1 & GC1 & BF1).
    eapply HK.
    + split; [exact ACT1|]. split; [reflexivity|]. split; [exact (GP_taf _ _ _ TAF)|]. right.
      pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1))))) _ _ _ Hg) as GO.
      pose proof (g_stride _ _ _ _ _ _ GO ltac:(rewrite SC; lia)) as (GS & _ & _). rewrite SC in GS.
      exists g, bg, ai. split; [exact Hidx|]. split; [exact HA|]. split; [exact Hg|]. split; [exact SC|].
      split; [lia|]. split; [intros Hs28; destruct GS; lia|]. split; [exact INV1|]. apply TF0_TF2. exact TF1.
    + exact QP1.
    + intros c Hc. apply GC1. lia.
    + exact BF1.
Qed.
End SLOTQ.
