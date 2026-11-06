(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Decode.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import STree Malloc MallocCtrl KInv KStep
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_Cnt
  LB_Tables LB_Inv LB_Sum LB_Kernel LB_Embed LB_Bound LB_WNtf LB_XferF LB_Tree LB_QM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma gmetas_ext st st1 : s_groups st1 = s_groups st -> gmetas st1 = gmetas st.
Proof. intros E. unfold gmetas, groups_l. rewrite E. reflexivity. Qed.

Lemma gcnt_frame st st1 c : s_groups st1 = s_groups st ->
  (forall m, (exists b, hosts st b m) -> geom (MR st1 m) = geom (MR st m)) -> gcnt st1 c = gcnt st c.
Proof.
  intros EG GEO. rewrite !gcnt_gmetas, (gmetas_ext st st1 EG). apply zsum_map_ext. intros [m b] Hin. cbn.
  apply gmetas_in in Hin as [ai Hb]. pose proof (GEO m (ex_intro _ b (ex_intro _ ai Hb))) as G. unfold geom in G. inversion G.
  unfold cnt_of. rewrite H1, H2. reflexivity.
Qed.

Lemma AQ_frame st st1 BL P : s_groups st1 = s_groups st ->
  (forall m, (exists b, hosts st b m) -> geom (MR st1 m) = geom (MR st m)) -> ncarved st1 <= NCAP P ->
  AQ st BL P -> AQ st1 BL P.
Proof.
  intros EG GEO NC A. destruct A as [A1 A2 A3 A4 A5]. constructor; auto.
  intros c Hc. rewrite (gcnt_frame st st1 c EG GEO). exact (A2 c Hc).
Qed.

Lemma am_bytes X st L BL LS d : INVL X st L BL LS -> QM X st d ->
  gm L + BB L <= group_bytes st + PGSZ * (5 * (ncarved st / 101) + 6)
  /\ meta_bytes st <= PGSZ * (if c_meta_alloc_shift (s_ctx st) <? 1 then 0 else 2 ^ (c_meta_alloc_shift (s_ctx st) + 1) - 2)
  /\ PGSZ * brk_pages st <= PGSZ * (ncarved st / 101 + 2)
  /\ gm L + BB L <= group_bytes st + meta_bytes st + PGSZ * brk_pages st.
Proof.
  intros INV Q. pose proof (proj1 INV) as IR. destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6].
  pose proof (ledger_bound X st L BL LS INV) as LB.
  pose proof (meta_bytes_bound4 st Q4 Q5 Q6) as M4. pose proof (meta_bytes_pow st Q4 Q5) as MP.
  pose proof (brk_pages_boundQ X st L IR Q3) as BP. unfold PGSZ in *. lia.
Qed.

Lemma div101_mono n N : 0 <= n <= N -> 5 * (n / 101) <= 5 * N / 101.
Proof. intros H. apply Z.div_le_lower_bound; [lia|]. pose proof (Z.div_mod n 101 ltac:(lia)). pose proof (Z.mod_pos_bound n 101 ltac:(lia)). pose proof (Z.div_le_mono n N 101 ltac:(lia) ltac:(lia)). nia. Qed.

Section AMQ.
Variables (T : Type) (BL : list blk) (P : Z -> Z) (B : Z) (Post : mled -> T -> Prop) (k : mstate -> optr -> M T) (bail : M T).
Variables (X : extras) (st0 : mstate) (L0 : mled) (LS0 : lhead -> list aptr).
Hypothesis INV0 : INVL X st0 L0 BL LS0.
Hypothesis SG0 : SG st0 BL.
Hypothesis HAQ0 : AQ st0 BL P.
Hypothesis ROOM0 : c_free_meta_head (s_ctx st0) = None -> ncarved st0 + 1 <= NCAP P.
Hypothesis HB : group_bytes st0 + PGSZ * (5 * NCAP P / 101 + 8) <= B.
Hypothesis KN : forall st1 L1 LS1, INVL X st1 L1 BL LS1 -> AM_frame st0 st1 -> L_frame L0 L1 ->
  SINV X st1 BL -> AQ st1 BL P -> (forall c, gcnt st1 c = gcnt st0 c) ->
  (forall m, (exists b, hosts st0 b m) -> geom (MR st1 m) = geom (MR st0 m)) -> fqtree B L1 (k st1 None) Post.
Hypothesis KS : forall st1 L1 LS1 m, INVL (xidle X (m :: x_idle X)) st1 L1 BL LS1 -> ~ In m (x_idle X) -> AM_frame st0 st1 -> L_frame L0 L1 ->
  SINV (xidle X (m :: x_idle X)) st1 BL -> AQ st1 BL P -> ncarved st1 <= ncarved st0 + 1 -> (forall c, gcnt st1 c = gcnt st0 c) ->
  (forall x, (exists b, hosts st0 b x) -> geom (MR st1 x) = geom (MR st0 x)) ->
  fqtree B L1 (k st1 (Some m)) Post.

Definition QT (Y : extras) (st : mstate) (d : Z) : Prop :=
  QM Y st d /\ ncarved st = ncarved st0 /\ group_bytes st = group_bytes st0
  /\ (forall m, (exists b, hosts st0 b m) -> geom (MR st m) = geom (MR st0 m)).

Lemma SV0 : forall s m i, s_slots st0 !! s = Some (m, i) -> exists b, hosts st0 b m.
Proof. intros s m i H. exact (proj1 (is_valid _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV0)))))) _ _ _ H)). Qed.

Lemma SG_of st : AM_frame st0 st -> (forall m, (exists b, hosts st0 b m) -> geom (MR st m) = geom (MR st0 m)) -> SG st BL.
Proof. intros AF GEO. apply (SG_frame st0 st BL (amf_groups _ _ AF) (amf_slots _ _ AF) GEO SV0 SG0). Qed.

Lemma exit_none st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L -> QT X st 0 -> fqtree B L (k st None) Post.
Proof.
  intros INV AF LF (Q & NC & GB & GEO). apply (KN st L LS INV AF LF).
  - apply SINV_split. split; [exact (SG_of st AF GEO)| exact Q].
  - apply (AQ_frame st0 st BL P (amf_groups _ _ AF) GEO); [rewrite NC; exact (aq_carved _ _ _ HAQ0)| exact HAQ0].
  - intros c. exact (gcnt_frame st0 st c (amf_groups _ _ AF) GEO).
  - exact GEO.
Qed.

Lemma bound_of st L LS d extra : INVL X st L BL LS -> QT X st d -> 0 <= extra <= 2 * PGSZ ->
  gm L + BB L + extra <= B.
Proof.
  intros INV (Q & NC & GB & GEO) HE. destruct (am_bytes X st L BL LS d INV Q) as (A & _).
  rewrite NC, GB in A. pose proof (div101_mono (ncarved st0) (NCAP P) ltac:(pose proof (ncarved_nonneg st0); pose proof (aq_carved _ _ _ HAQ0); lia)). unfold PGSZ in *. lia.
Qed.

Lemma am_take_fq st L LS : ncarved st0 + 1 <= NCAP P -> INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  0 < c_avail_meta_count (s_ctx st) -> QT X st 0 -> fqtree B L (am_take st k bail) Post.
Proof.
  intros ROOM INV AF LF HC (Q & NC & GB & GEO).
  destruct (ia_avail _ (proj1 (proj2 INV))) as [A1 A2]. destruct (A2 HC) as (a & Ht & Ea & FREE).
  set (m := mslot a (NSLOTS - c_avail_meta_count (s_ctx st))) in *.
  pose proof (take_fresh X st L BL LS m INV HC Ea) as FRm.
  rewrite (am_take_unfold st m k bail Ea).

  destruct (am_take_ok X st L BL LS INV HC (fun s o => ret (s, o)) (ret (st, @None aptr))) as (m' & st2 & E2 & INV2 & AF2 & NI).
  rewrite (am_take_unfold st m _ _ Ea) in E2. assert (Em : m' = m) by (inversion E2; reflexivity). assert (Es : st2 = take_st st m) by (inversion E2; reflexivity). subst m' st2.
  destruct (QM_take X st m 0 FRm Q) as (Q2 & NC2 & RG2 & AP2 & MR2).
  assert (GEO2 : forall x, (exists b, hosts st0 b x) -> geom (MR (take_st st m) x) = geom (MR st0 x)).
  { intros x Hx. rewrite MR2; [exact (GEO x Hx)|]. intros ->.
    destruct Hx as [b [ai Hb]]. pose proof (im_hdr _ _ _ (proj1 (proj2 (proj2 INV0))) _ _ Hb) as (m1 & Em1 & MEM & _). cbn in Em1. assert (m1 = m) by congruence. subst m1.
    pose proof (GEO m (ex_intro _ b (ex_intro _ ai Hb))) as G. assert (Z0 : m_mem (MR st m) = None) by (unfold MR, get_meta_rec; rewrite FRm; reflexivity). unfold geom in G. rewrite Z0, MEM in G. congruence. }
  apply (KS (take_st st m) L LS m INV2 NI (amf_trans _ _ _ AF AF2) LF).
  - apply SINV_split. split; [| exact Q2]. exact (SG_of (take_st st m) (amf_trans _ _ _ AF AF2) GEO2).
  - apply (AQ_frame st0 (take_st st m) BL P (amf_groups _ _ (amf_trans _ _ _ AF AF2)) GEO2); [| exact HAQ0].
    rewrite NC2, NC. exact ROOM.
  - rewrite NC2, NC. lia.
  - intros c. exact (gcnt_frame st0 (take_st st m) c (amf_groups _ _ (amf_trans _ _ _ AF AF2)) GEO2).
  - exact GEO2.
Qed.

Lemma am_carve_fq s p L LS : ncarved st0 + 1 <= NCAP P -> INVL X s L BL LS ->
  c_avail_meta_areas (s_ctx s) = Some (aadd p 4096) -> s_areas s !! p = None -> (forall k, 0 <= k < NSLOTS -> s_metas s !! mslot p k = None) ->
  PGSZ <= snd p -> snd p mod PGSZ = 0 -> c_init_done (s_ctx s) = 1 ->
  AM_frame st0 s -> L_frame L0 L -> QT X s 101 -> c_avail_meta_count (s_ctx s) = 0 ->
  fqtree B L (am_take (carve_rest s p) k bail) Post.
Proof.
  intros ROOM INV H1 H2 H3 H4 H5 H6 AF LF (Q & NC & GB & GEO) HK.
  destruct (INVL_carve X s L BL LS p INV H1 H2 H3 H4 H5 H6) as (INV' & AF' & HC).
  destruct (carve_rest_q s p) as (R1 & R2 & R3 & R4 & R5 & R6).
  eapply am_take_fq; [exact ROOM| exact INV'| exact (amf_trans _ _ _ AF AF')| exact LF| exact HC|].
  split; [exact (QM_carve_rest X s p 101 Q HK ltac:(lia))|]. split; [rewrite (ncarved_ext s _ R2); exact NC|].
  split; [rewrite (group_bytes_ext s _ R1); exact GB|]. intros m Hm. rewrite <- (GEO m Hm). unfold MR, get_meta_rec. rewrite R2. reflexivity.
Qed.

Lemma am_finish_fq st L LS : ncarved st0 + 1 <= NCAP P -> INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  0 < c_avail_meta_area_count (s_ctx st) -> c_init_done (s_ctx st) = 1 -> QT X st 0 -> c_avail_meta_count (s_ctx st) = 0 ->
  fqtree B L (am_finish st true k bail) Post.
Proof.
  intros ROOM INV AF LF HC HI QT0 HK. pose proof QT0 as (Q & NC & GB & GEO).
  destruct (ir_cursor _ _ _ (proj1 INV)) as (C1 & C2 & C3).
  destruct (c_avail_meta_areas (ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 HC EC)].
  destruct (C3 _ _ EC) as (r & Hr & K & P1 & P2 & P3 & P4).
  unfold am_finish. rewrite EC. cbn [snd]. rewrite (proj2 (Z.eqb_eq _ _) P2). cbn [negb].
  apply fqtree_vis; [reflexivity| reflexivity| exact (ma_event_pre X st L BL LS rid off INV EC HC)| | |].
  - intros z Hz. unfold event_post. pose proof (bound_of st L LS 0 0 INV QT0 ltac:(unfold PGSZ; lia)) as B0.
    destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); [rewrite gm_bump, BB_set_metas|]; lia.
  - intros a Ha. cbn in Ha. rewrite Ha. cbn [negb].
    change (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None)
      with (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None).
    cbn [event_post]. destruct ((a =? 0) || (a =? TWO64 - ENOSYS)).
    + rewrite am_carve_eq.
      destruct (INVL_meta_adv X st L BL LS rid off INV EC HC) as (INV' & F1 & F2 & F3 & F4 & F5 & F6 & AF').
      eapply am_carve_fq; [exact ROOM| exact INV'| exact F1| exact F2| exact F3| exact F4| exact F5| rewrite F6; exact HI| exact (amf_trans _ _ _ AF AF')| | |].
      * destruct LF; constructor; assumption.
      * split; [| split; [exact NC| split; [exact GB| exact GEO]]].
        replace 101 with (0 + 101) by reflexivity. apply (QM_adv X st L rid off r 0 (proj1 INV) EC Hr K P2 Q).
      * exact HK.
    + eapply exit_none; [exact INV| exact AF| exact LF| exact QT0].
  - intros a Ha. cbn in Ha. rewrite Ha. exact I.
Qed.

Lemma am_after_brk_fq st L LS : ncarved st0 + 1 <= NCAP P -> INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L ->
  c_init_done (s_ctx st) = 1 -> QT X st 0 -> c_avail_meta_count (s_ctx st) = 0 ->
  fqtree B L (am_after_brk st true k bail) Post.
Proof.
  intros ROOM INV AF LF HI QT0 HK. pose proof QT0 as (Q & NC & GB & GEO). unfold am_after_brk.
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx st)) 0) as [HC|HC].
  -
    destruct (am_bytes X st L BL LS 0 INV Q) as (A1 & A2 & A3 & A4).
    destruct (nm_n X st L BL LS INV) as [En N2].
    pose proof (div101_mono (ncarved st0) (NCAP P) ltac:(pose proof (ncarved_nonneg st0); pose proof (aq_carved _ _ _ HAQ0); lia)) as DM.
    assert (LEN : mmap_len (Z.shiftl 2 (c_meta_alloc_shift (s_ctx st)) * PGSZ) = Z.shiftl 2 (c_meta_alloc_shift (s_ctx st)) * PGSZ).
    { apply mmap_len_of_aligned; [unfold PGSZ; lia| unfold PGSZ; apply Z_mod_mult]. }
    assert (MAIN : gm L + BB L + Z.shiftl 2 (c_meta_alloc_shift (s_ctx st)) * PGSZ <= B).
    { rewrite En in *. rewrite Z.pow_add_r in * by (try lia; pose proof (proj1 (ir_shift _ _ _ (proj1 INV))); lia). change (2 ^ 1) with 2 in *.
      rewrite NC, GB in *.
      destruct (Z.ltb_spec (c_meta_alloc_shift (s_ctx st)) 1) as [S0|S1].
      - assert (E0 : c_meta_alloc_shift (s_ctx st) = 0) by (pose proof (proj1 (ir_shift _ _ _ (proj1 INV))); lia). rewrite E0 in *. cbn in *. unfold PGSZ in *. lia.
      - pose proof (exhausted_shift X st L 0 (proj1 INV) Q (ltac:(unfold ctx in HC; exact HC)) HK ltac:(lia) S1) as EX. rewrite NC in EX.
        set (t := 2 ^ c_meta_alloc_shift (s_ctx st)) in *.
        assert (TQ : t - 1 <= ncarved st0 / 101) by (apply Z.div_le_lower_bound; lia).
        unfold PGSZ in *. lia. }
    apply fqtree_vis_map; [exact (nm_event_pre X st L BL LS INV)| | right; unfold ctx; rewrite LEN; lia| |].
    +
      intros z Hz. unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_NONE =? PROT_NONE) with true. cbn iota.
      pose proof (proj2 (nm_n X st L BL LS INV)) as N2'.
      destruct (is_err z); [unfold PGSZ in *; lia|]. rewrite gm_add_meta, BB_set_metas. unfold ctx. rewrite LEN. lia.
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. cbn [negb].
      unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_NONE =? PROT_NONE) with true. cbn [andb].
      destruct (is_err a) eqn:NE.
      * eapply exit_none; [exact INV| exact AF| exact LF| exact QT0].
      * destruct (INVL_new_meta X st L BL LS a INV HC Ha NE) as (INV' & HC' & HI' & AF').
        destruct (QM_new_meta X st L BL LS a 0 INV HC HK Q ltac:(lia)) as (Q2 & NC2 & AP2 & GB2 & MB2 & BP2 & MR2 & SH2 & EX2).
        eapply am_finish_fq; [exact ROOM| exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| exact HC'| rewrite HI'; exact HI| | reflexivity || exact HK].
        split; [exact Q2|]. split; [rewrite NC2; exact NC|]. split; [rewrite GB2; exact GB|]. intros m Hm. rewrite MR2. exact (GEO m Hm).
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. exact I.
  - eapply am_finish_fq; [exact ROOM| exact INV| exact AF| exact LF| pose proof (proj1 (ir_cursor _ _ _ (proj1 INV))); unfold ctx in HC; lia| exact HI| exact QT0| exact HK].
Qed.

Lemma QT_am_init Y st d : QT Y st d -> QT Y (am_init st) d.
Proof.
  intros (Q & NC & GB & GEO). unfold am_init. destruct (c_init_done (ctx st) =? 0); [| split; auto].
  split; [| split; [exact NC| split; [exact GB| exact GEO]]].
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]; constructor; cbn -[apages ncarved]; auto.
  all: replace (apages (upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st)) with (apages st) by (apply apages_ext; reflexivity); exact Q2.
Qed.

Lemma QT_brk_dead Y st d : QT Y st d -> QT Y (upd_ctx (set_brk BrkDead) st) d.
Proof.
  intros (Q & NC & GB & GEO). split; [| split; [exact NC| split; [exact GB| exact GEO]]].
  destruct Q as [Q1 Q2 Q3 Q4 Q5 Q6]; constructor; cbn -[apages ncarved]; auto.
  all: replace (apages (upd_ctx (set_brk BrkDead) st)) with (apages st) by (apply apages_ext; reflexivity); exact Q2.
Qed.

Theorem alloc_meta_fq st L LS : INVL X st L BL LS -> AM_frame st0 st -> L_frame L0 L -> QT X st 0 ->
  c_free_meta_head (s_ctx st) = c_free_meta_head (s_ctx st0) ->
  fqtree B L (alloc_meta st k bail) Post.
Proof.
  intros INV1 AF0 LF QT1 EFH0.
  assert (EFH1 : c_free_meta_head (s_ctx (am_init st)) = c_free_meta_head (s_ctx st0)) by (unfold am_init; destruct (c_init_done (ctx st) =? 0); exact EFH0).
  destruct (INVL_am_init X st L BL LS INV1) as (INV & HI & AFi).
  pose proof (amf_trans _ _ _ AF0 AFi) as AF. pose proof (QT_am_init X st 0 QT1) as QT0. clear AF0 AFi INV1 QT1.
  unfold alloc_meta. fold (am_init st). set (s := am_init st) in *. clearbody s.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH). pose proof QT0 as (Q & NC & GB & GEO).

  destruct (c_free_meta_head (ctx s)) as [m|] eqn:EFH.
  { pose proof (il_head _ _ IL LFree) as HH. cbn in HH. unfold ctx in EFH. rewrite EFH in HH.
    destruct (LS LFree) as [|m' rest] eqn:ELS; [discriminate|]. cbn in HH. inversion HH. subst m'.
    pose proof (INVL_dequeue X (xidle X (m :: x_idle X)) s L BL LS m LFree [] rest INV ltac:(rewrite ELS; reflexivity) ltac:(right; split; reflexivity)) as INV2.
    destruct (dequeue_frame LFree m s) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & FC).
    destruct (am_reuse_q X s L BL LS m rest 0 INV ELS Q) as (Q2 & NC2 & RG2 & AP2 & DD).
    assert (AF2 : AM_frame st0 (dequeue LFree m s)).
    { eapply amf_trans; [exact AF|]. destruct FC. constructor; auto; try congruence.
      all: try (intros sc; change (active (dequeue LFree m s) sc) with (get_head (dequeue LFree m s) (LActive sc)); rewrite dequeue_head;
                destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]).
      all: try (intros sc; unfold usage, ctx; rewrite cb_usage; reflexivity).
      all: try (intros rid r H _; rewrite F1; exact H).
      all: rewrite ?F3; lia. }
    assert (GEO2 : forall x, (exists b, hosts st0 b x) -> geom (MR (dequeue LFree m s) x) = geom (MR st0 x)).
    { intros x Hx. rewrite <- (GEO x Hx). apply geom_data. apply DD. }
    eapply KS; [exact INV2| | exact AF2| exact LF| | | | | exact GEO2].
    - intros Hin. apply (proj2 (im_idle _ _ _ IM m Hin)). exists LFree. rewrite ELS. left. reflexivity.
    - apply SINV_split. split; [exact (SG_of _ AF2 GEO2)| exact Q2].
    - apply (AQ_frame st0 _ BL P (amf_groups _ _ AF2) GEO2); [rewrite NC2, NC; exact (aq_carved _ _ _ HAQ0)| exact HAQ0].
    - rewrite NC2, NC. lia.
    - intros c. exact (gcnt_frame st0 _ c (amf_groups _ _ AF2) GEO2). }

  assert (ROOM : ncarved st0 + 1 <= NCAP P) by (apply ROOM0; rewrite <- EFH1; unfold ctx in EFH; exact EFH).
  destruct (Z.eqb_spec (c_avail_meta_count (ctx s)) 0) as [HAC|HAC]; cbn [negb].
  2:{ eapply am_take_fq; [exact ROOM| exact INV| exact AF| exact LF| pose proof (proj1 (ia_avail _ IA)); unfold ctx in HAC; lia| exact QT0]. }

  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx s)) 0) as [HC|HC]; cbn [andb].
  2:{ eapply am_after_brk_fq; [exact ROOM| exact INV| exact AF| exact LF| exact HI| exact QT0| unfold ctx in HAC; exact HAC]. }
  pose proof (ir_brk _ _ _ IR) as IBK. unfold ctx. destruct (c_brk (s_ctx s)) as [| |rid off] eqn:EBRK; cbn [negb].
  -
    destruct IBK as [BP NB].
    assert (BR0 : ld_brkreg L = None).
    { destruct (ld_brkreg L) as [[b l]|] eqn:E; [| reflexivity]. exfalso.
      destruct (proj1 (ir_brkreg _ _ _ IR b l) E) as (q & rq & Hq & Kq & _). exact (NB q rq Hq Kq). }
    assert (BB0 : BB L = 0) by (unfold BB; rewrite BP, BR0; reflexivity).
    pose proof (bound_of s L LS 0 (2 * PGSZ) INV QT0 ltac:(unfold PGSZ; lia)) as BND. rewrite BB0 in BND. unfold PGSZ in BND.
    apply fqtree_vis; [reflexivity| reflexivity| left; auto| | |].
    { intros cur Hc. cbn [event_post Z.eqb]. rewrite gm_set_brkph. unfold BB. cbn. rewrite BR0. lia. }
    2:{ intros cur Hc. cbn in Hc. rewrite Hc. exact I. }
    intros cur Hc. cbn in Hc. rewrite Hc. cbn [negb]. cbn [event_post Z.eqb].
    set (L1 := KInv.set_brkph (BPQueried cur) L).
    set (base := round_up_pg cur). set (new := base + 2 * PGSZ).
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, base. pose proof (round_up_ge cur). unfold brk0_answer_ok in Hc.
      apply Bool.andb_true_iff in Hc as [Hc _]. apply Bool.andb_true_iff in Hc as [Hc _]. apply Z.ltb_lt in Hc. unfold PGSZ. lia. }
    apply fqtree_vis; [reflexivity| reflexivity| right; left; exists cur; split; reflexivity| | |].
    { intros z Hz. unfold event_post. rewrite NZ. unfold L1. cbn [KInv.ld_brk KInv.set_brkph].
      destruct (z =? new); unfold BB; cbn; rewrite ?BR0; unfold gm in BND |- *; cbn in BND |- *; unfold PGSZ in *; lia. }
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [KInv.ld_brk KInv.set_brkph] in Hr.
      apply Bool.andb_true_iff in Hr as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ. unfold L1. cbn [KInv.ld_brk KInv.set_brkph].
      destruct (Z.eqb_spec r new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp.
        rewrite (lbrk_pages_ok_ext (KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. cbn [negb].
        apply fqtree_vis; [reflexivity| reflexivity| right; exists cur; cbn; repeat split; reflexivity| | |].
        { intros z Hz. unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false. cbn [andb].
          unfold BB, gm in BND |- *. cbn in BND |- *. unfold PGSZ in *. lia. }
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. cbn [negb]. unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false. cbn [andb].
           set (st1 := new_region RKBrk base (2 * PGSZ) s). destruct st1 as [s1 rid] eqn:ES1.
           assert (Erid : rid = s_next_rid s) by (unfold st1, new_region in ES1; inversion ES1; reflexivity).
           assert (Es1 : s1 = fst (new_region RKBrk base (2 * PGSZ) s)) by (unfold st1 in ES1; rewrite <- ES1 || idtac; unfold new_region in *; inversion ES1; reflexivity).
           subst rid s1.
           unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
           unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
           change (PGSZ mod PGSZ =? 0) with true. cbn [negb].
           rewrite am_carve_eq.
           destruct (INVL_brk_first X s L BL LS cur INV EBRK HC ltac:(exact Hp) (KInv.set_brkph (BPGuard cur) (KInv.set_brkph (BPQueried cur) L)) ltac:(repeat split; reflexivity))
             as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
           destruct (QM_brk_first X s L BL LS cur 0 INV EBRK HC HAC Q ltac:(lia)) as (Q3 & NC3 & AP3 & GB3 & MB3 & BP3 & MR3 & CK3 & _).
           eapply am_carve_fq; [exact ROOM| exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')| | | exact CK3].
           ++ destruct LF; constructor; assumption.
           ++ split; [exact Q3|]. split; [rewrite NC3; exact NC|]. split; [rewrite GB3; exact GB|]. intros x Hx. rewrite MR3. exact (GEO x Hx).
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. exact I.
      * destruct (INVL_brk_dead X s L (KInv.set_brkph BPDead (KInv.set_brkph (BPQueried cur) L)) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_fq; [exact ROOM| exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI| apply QT_brk_dead; exact QT0| cbn; exact HAC].
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [KInv.ld_brk KInv.set_brkph] in Hr.
      apply Bool.andb_false_iff in Hr. destruct Hr as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok cur new r); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (lbrk_pages_ok_ext (KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. exact I.
  -   eapply am_after_brk_fq; [exact ROOM| exact INV| exact AF| exact LF| exact HI| exact QT0| exact HAC].
  -
    destruct IBK as [BP (r & Hr & K & Elen)].
    pose proof (bg_event_pre X s L BL LS rid off INV EBRK) as PRE.
    set (old := conc s (rid, off)) in *. set (new := old + PGSZ) in *.
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, old, conc, get_region. rewrite Hr. cbn [fst snd]. pose proof (ir_shape _ _ _ IR _ _ Hr) as (S1 & _ & S3 & _). unfold PGSZ. lia. }
    assert (BR : ld_brkreg L = Some (r_base r, off)).
    { apply (proj2 (ir_brkreg _ _ _ IR (r_base r) off)). exists rid, r. auto. }
    assert (Eold : old = r_base r + off) by (unfold old, conc, get_region; rewrite Hr; cbn [fst snd]; reflexivity).
    pose proof (bound_of s L LS 0 PGSZ INV QT0 ltac:(unfold PGSZ; lia)) as BND.
    apply fqtree_vis; [reflexivity| reflexivity| exact PRE| | |].
    { intros z Hz. unfold event_post. rewrite NZ, BP, BR.
      assert (BBL : BB L = off) by (unfold BB; rewrite BP, BR; reflexivity). rewrite BBL in BND.
      destruct (z =? new).
      - rewrite gm_set_brkreg. unfold BB. cbn [ld_brk ld_brkreg set_brkreg]. rewrite BP. unfold PGSZ in *. lia.
      - rewrite gm_set_brkph. unfold BB. cbn [ld_brk ld_brkreg set_brkph]. rewrite BR. unfold PGSZ in *. lia. }
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_true_iff in Hz as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ, BP, BR.
      destruct (Z.eqb_spec z new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp. rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. cbn [negb].
        unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
        unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
        destruct (bg_region X s L BL LS rid off INV EBRK) as (r' & _ & _ & _ & _ & _ & _ & _ & OM & _).
        rewrite (proj2 (Z.eqb_eq _ _) OM). cbn [negb].
        rewrite am_carve_eq.
        destruct (INVL_brk_grow X s L BL LS rid off INV EBRK HC ltac:(exact Hp)) as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
        replace (conc s (rid, off) - off) with (r_base r) in INV' by (unfold conc, get_region; rewrite Hr; cbn [fst snd]; lia).
        destruct (QM_brk_grow X s L BL LS rid off 0 INV EBRK HC HAC Q ltac:(lia)) as (Q3 & NC3 & AP3 & GB3 & MB3 & BP3 & MR3 & CK3 & _).
        eapply am_carve_fq; [exact ROOM| exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')| | | exact CK3].
        -- destruct LF; constructor; assumption.
        -- split; [exact Q3|]. split; [rewrite NC3; exact NC|]. split; [rewrite GB3; exact GB|]. intros x Hx. rewrite MR3. exact (GEO x Hx).
      * destruct (INVL_brk_dead X s L (KInv.set_brkph BPDead L) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_fq; [exact ROOM| exact INV'| exact (amf_trans _ _ _ AF AF')| destruct LF; constructor; assumption| cbn; exact HI| apply QT_brk_dead; exact QT0| cbn; exact HAC].
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_false_iff in Hz. destruct Hz as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok old new z); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. exact I.
Qed.
End AMQ.
