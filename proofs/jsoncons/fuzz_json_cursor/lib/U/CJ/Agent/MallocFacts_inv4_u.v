(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Read MI_WFree
  MI_Pres2 MI_Pres3 MI_Pres4 MI_WFree2 MI_WNtf2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_Cnt MI_WTry2 MI_WGroup MI_TF2 MI_WSlot MI_WSlot2 MI_WSlot3 MI_WMalloc MI_Sim MI_Contracts MI_Fuel.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import MallocRep_u MallocTree_u MallocBlocks_u MallocFacts_A_u MallocFacts_B_u MallocFacts_AM_u MallocNat_u MallocFacts_AS_u
  MallocFacts_inv_u MallocFacts_inv2_u MallocFacts_inv3_u.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Section GF.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis ZB : x_zomb X = [].
Hypothesis NFR : x_fresh X = None.

Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let ISH := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

Lemma lmem_listed m h : In m (LS h) -> live_group st m -> lmem (strip st) m.
Proof.
  intros Hin [b Hb]. unfold lmem. rewrite !get_meta_rec_strip. fold (MR st m).
  split; [rewrite (hosts_mem _ _ _ IM _ _ Hb); discriminate|].
  split; [exact (listed_next _ _ _ _ _ INV m h Hin)|].
  destruct (lists_prev_in st LS (old_lists _ _ _ _ _ INV) h m Hin) as (y & _ & E & _). rewrite E. discriminate.
Qed.

Lemma mem_live g b : m_mem (MR st g) = Some b -> hosts st b g.
Proof. intros H. exact (mem_hosts X st L BL LS INV ZB g b H). Qed.

Lemma linked_group_listed g b : m_mem (MR st g) = Some b -> m_next (MR st g) <> None ->
  In g (LS (LActive (m_sizeclass (MR st g)))).
Proof.
  intros Hb Hn. destruct (proj2 (proj1 (il_link _ _ IL g)) Hn) as [h Hh].
  destruct h as [sc|].
  - destruct (il_active _ _ IL sc g Hh) as (_ & _ & <-). exact Hh.
  - exfalso. apply (free_not_live _ _ _ _ _ INV g Hh). exists b. exact (mem_live _ _ Hb).
Qed.

Lemma l_lists : fact_lists (strip st).
Proof.
  split; [| split].
  - intros sc g H. rewrite active_strip in H. pose proof (head_listed _ _ _ _ _ INV (LActive sc) g H) as Hin.
    destruct (il_active _ _ IL sc g Hin) as (_ & Hl & _). exact (lmem_listed _ _ Hin Hl).
  - intros g n Hm Hn. rewrite !get_meta_rec_strip in *. fold (MR st g) (MR st n) in *.
    destruct (m_mem (MR st g)) as [b|] eqn:Hb; [| congruence].
    pose proof (linked_group_listed _ _ Hb ltac:(rewrite Hn; discriminate)) as Hg.
    pose proof (next_listed _ _ _ _ _ INV _ g n Hg Hn) as Hn'.
    destruct (il_active _ _ IL _ n Hn') as (_ & Hl & Esc). split; [exact (lmem_listed _ _ Hn' Hl)| exact Esc].
  - intros g p Hm Hp. rewrite !get_meta_rec_strip in *. fold (MR st g) (MR st p) in *.
    destruct (m_mem (MR st g)) as [b|] eqn:Hb; [| congruence].
    destruct (m_next (MR st g)) as [x|] eqn:Ex; [| pose proof (proj2 (il_link _ _ IL g) Ex) as P; rewrite Hp in P; discriminate].
    pose proof (linked_group_listed _ _ Hb ltac:(rewrite Ex; discriminate)) as Hg.
    pose proof (prev_listed _ _ _ _ _ INV _ g p Hg Hp) as Hp'.
    destruct (il_active _ _ IL _ p Hp') as (_ & Hl & Esc). split; [exact (lmem_listed _ _ Hp' Hl)| exact Esc].
Qed.

Lemma l_freelist : fact_freelist (strip st).
Proof.
  intros h Hh. rewrite ctx_strip in Hh. rewrite !get_meta_rec_strip. fold (MR st h).
  pose proof (head_listed _ _ _ _ _ INV LFree h Hh) as Hin.
  assert (MS : forall m, In m (LS LFree) -> meta_slot (strip st) m).
  { intros m Hm. destruct (listed_meta_slot X st L BL LS INV m LFree Hm) as (a & ar & k & Ha & Hk & E). exists a, ar, k. auto. }
  split; [exact (MS h Hin)|].
  pose proof (il_free _ _ IL h Hin) as E. split; [rewrite E; reflexivity|].
  split; [exact (listed_next _ _ _ _ _ INV h LFree Hin)|].
  destruct (lists_prev_in st LS (old_lists _ _ _ _ _ INV) LFree h Hin) as (p & Hp & Ep & Np).
  exists p. split; [exact Ep|]. split; [exact (MS p Hp)|]. rewrite !get_meta_rec_strip. fold (MR st p).
  pose proof (il_free _ _ IL p Hp) as Ep'. split; [rewrite Ep'; reflexivity|]. rewrite Np. discriminate.
Qed.
Lemma l_mw : fact_mw (strip st).
Proof.
  intros g. rewrite !get_meta_rec_strip. fold (MR st g).
  destruct (m_mem (MR st g)) as [b|] eqn:Hb.
  - destruct (hosts_ok _ _ _ IG _ _ (mem_live _ _ Hb)) as (ai & Hg & GO).
    pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
    pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_maplen _ _ _ _ _ _ GO) as ML.
    assert (AV : m_avail (MR st g) < 2 ^ 32).
    { apply bits_below_bound; [exact M1| lia|]. intros i Hi Ht. pose proof (M3 i Hi Ht). lia. }
    assert (FR : m_freed (MR st g) < 2 ^ 32).
    { apply bits_below_bound; [exact M2| lia|]. intros i Hi Ht. pose proof (M4 i Hi Ht). lia. }
    assert (MLB : m_maplen (MR st g) < 2 ^ 52).
    { destruct (Z.eq_dec (m_maplen (MR st g)) 0) as [->|NZ]; [lia|].
      destruct (g_top _ _ _ _ _ _ GO NZ) as (_ & r & Hr & _ & E & _).
      destruct (ir_shape _ _ _ IR _ _ Hr) as (_ & _ & _ & LT & _). pose proof (round_up_pg_spec (r_len r)). unfold LEN_MAX in LT. lia. }
    split; [| lia]. unfold mw_ok. split; [exact LI|]. split; [rewrite (g_freeable _ _ _ _ _ _ GO); lia|].
    split; [| lia]. destruct (g_sc _ _ _ _ _ _ GO) as [[S1 _]|(S1 & _)]; lia.
  - rewrite (im_zero _ _ _ IM g Hb). cbn. unfold mw_ok. cbn. lia.
Qed.

Lemma l_host_stride : fact_host_stride (strip st).
Proof.
  intros g b Hb Hsc. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
  destruct (hosts_ok _ _ _ IG _ _ (mem_live _ _ Hb)) as (ai & Hg & GO).
  destruct (g_stride _ _ _ _ _ _ GO ltac:(lia)) as (S1 & S2 & S3).
  unfold get_stride in *. destruct (m_last_idx (MR st g) =? 0) eqn:E0; [| reflexivity].
  destruct (m_maplen (MR st g) =? 0) eqn:EM; cbn [andb negb] in *; [reflexivity|].
  apply Z.eqb_eq in E0. apply Z.eqb_neq in EM. destruct (S2 E0) as [_ S27].
  assert (Esc : m_sizeclass (MR st g) = 27) by lia. rewrite Esc in *. change (size_class 27) with 255 in *.
  destruct S1 as [S1|S1]; [| lia].
  pose proof (g_maplen _ _ _ _ _ _ GO). unfold UNIT in *. lia.
Qed.

Lemma l_links : fact_links (strip st).
Proof.
  intros g Hg. unfold lmem in Hg. rewrite !get_meta_rec_strip in *. fold (MR st g) in *. destruct Hg as (Hm & Hn & Hp).
  destruct (c_links X st L BL LS INV) as [CN CP _ _].
  split.
  - intros n E. rewrite get_meta_rec_strip. exact (proj1 (CN g n E)).
  - intros p E. rewrite get_meta_rec_strip. exact (proj1 (CP g p E)).
Qed.

Lemma l_sc0_full : fact_sc0_full (strip st).
Proof.
  intros g b gh Hb Hgh Hsc. rewrite s_groups_strip in Hgh. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
  pose proof (mem_live _ _ Hb) as Hh. destruct (hosts_ok _ _ _ IG _ _ Hh) as (ai & Hg & GO).
  rewrite Hg in Hgh. inversion Hgh; subst gh. cbn. exact (g_full0 _ _ _ _ _ _ GO Hsc).
Qed.

Lemma l_bit_stride : fact_bit_stride (strip st).
Proof.
  intros g b i Hb Hi Hbits Hsc. rewrite !get_meta_rec_strip in *. fold (MR st g) in *.
  destruct (hosts_ok _ _ _ IG _ _ (mem_live _ _ Hb)) as (ai & Hg & GO).
  destruct (Z.lt_ge_cases (get_stride (MR st g)) (UNIT * size_class (m_sizeclass (MR st g)))) as [LT|GE]; [| exact GE].
  exfalso. destruct (g_under _ _ _ _ _ _ GO ltac:(rewrite NFR; discriminate) Hsc LT) as [A0 F0].
  rewrite A0, F0, !Z.bits_0 in Hbits. discriminate Hbits.
Qed.

Lemma inv_lfacts : LFACTS (strip st).
Proof. constructor; [exact l_lists| exact l_freelist| exact l_mw| exact l_host_stride| exact l_links| exact l_sc0_full| exact l_bit_stride]. Qed.

Lemma inv_ghdr_unk : fact_ghdr_unk st.
Proof.
  intros b gh o Hb Ho. destruct (hdr_hosts X st L BL LS INV b gh Hb) as [m Hm].
  exact (ish_ghdr _ _ ISH b m o Hm ltac:(lia)).
Qed.

Variable resv : list (Z * Z).
Variable LB : list block.
Hypothesis CR : CORR st LB BL.
Hypothesis RESV : ld_resv L = resv.

Local Ltac inst f :=
  first [ exact (f _ _ _ _ _ INV) | exact (f _ _ _ _ _ INV ZB) | exact (f _ _ _ _ _ INV ZB NFR)
        | exact (f _ _ _ _ _ INV _ CR) | exact (f _ _ _ _ _ INV ZB _ CR) | exact (f _ _ _ _ _ INV ZB NFR _ CR) ].

Lemma inv_mfacts : @MFACTS_g resv st LB.
Proof.
  constructor.
  - inst LB_blocks_ok.
  - inst LB_nodup.
  - inst f_ticks.
  - rewrite <- RESV. symmetry. exact (ir_resv _ _ _ IR).
  - inst f_ctx.
  - inst f_active.
  - inst f_gmeta.
  - inst f_avail_clear.
  - inst f_hdr0.
  - inst f_free_clear.
  - inst f_hdr_clear.
  - inst f_usage.
  - inst f_masks.
  - inst f_maplen.
  - inst f_slots.
  - inst f_slots_complete.
  - inst f_ptrs.
  - inst f_blk_unknown.
  - inst f_blocks_disjoint.
  - inst f_cell_ticks.
Qed.

Lemma inv_istf : @ISTF_g resv st LB.
Proof. constructor; [exact inv_mfacts| exact inv_lfacts| exact inv_ghdr_unk]. Qed.

Lemma frontier_fresh rid r o : s_regions st !! rid = Some r -> frontier st rid r <= o -> fresh_above st rid o.
Proof.
  intros Hr Ho q Hq Hoq. split.
  - exact (proj1 (above_frontier X st L BL LS rid r q INV Hr Hq ltac:(lia))).
  - destruct (s_metas st !! q) as [mr|] eqn:E; [| reflexivity]. exfalso.
    destruct (ia_metas _ IA _ _ E) as (a & ar & k & Ha & Hk & Em).
    pose proof (proj2 (above_frontier X st L BL LS rid r a INV Hr ltac:(rewrite Em in Hq; exact Hq)
                  ltac:(rewrite Em in Hoq; unfold mslot, aadd in Hoq; cbn in Hoq; unfold AREA_HDR, META_SIZE, NSLOTS in *;
                        destruct (ia_areas _ IA _ _ Ha) as ((r' & Hr' & _ & _ & _ & F) & _);
                        rewrite Em in Hq; unfold mslot, aadd in Hq; cbn in Hq; rewrite Hq, Hr in Hr'; inversion Hr'; subst r'; rewrite Hq in F; unfold PGSZ in F; lia)) k Hk) as N.
    rewrite <- Em, E in N. discriminate N.
Qed.

Hypothesis SEC : s_secret st = secret_val.

Lemma inv_ampre : @AMpre_g _ resv st.
Proof.
  pose proof (ia_secret _ IA) as [S0 SD]. pose proof (ia_avail _ IA) as [AC AV]. pose proof (ir_cursor _ _ _ IR) as (C1 & C2 & C3).
  assert (RB : forall rid r, s_regions st !! rid = Some r -> 0 < r_len r < 2 ^ 47).
  { intros rid r Hr. destruct (ir_shape _ _ _ IR _ _ Hr) as (B0 & _ & L0 & _ & CE & _). pose proof (round_up_ge (r_len r)). pose_ceil. lia. }
  constructor.
  -   unfold ctx. destruct SD as [(_ & E & _)|[_ E]]; rewrite E; lia.
  - unfold ctx. destruct SD as [(E & _)|[E _]]; rewrite E; auto.
  - exact SEC.
  - unfold ctx. exact AC.
  - unfold ctx. split; [exact C1|]. destruct (Z.eq_dec (c_avail_meta_area_count (s_ctx st)) 0) as [E|NE]; [rewrite E; lia|].
    destruct (c_avail_meta_areas (s_ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 ltac:(lia) eq_refl)].
    destruct (C3 rid off eq_refl) as (r & Hr & _ & P1 & _ & E & _). pose proof (RB _ _ Hr). unfold PGSZ in *. nia.
  - unfold ctx. destruct (ir_shift _ _ _ IR) as [SH0 [E|(rid & r & Hr & _ & E)]]; [lia|].
    pose proof (RB _ _ Hr) as [_ LT]. rewrite E in LT. unfold PGSZ in LT. change 4096 with (2 ^ 12) in LT.
    split; [exact SH0|]. destruct (Z.le_gt_cases (c_meta_alloc_shift (s_ctx st)) 38) as [|GT]; [assumption|]. exfalso.
    assert (2 ^ 39 <= 2 ^ c_meta_alloc_shift (s_ctx st)) by (apply Z.pow_le_mono_r; lia). nia.
  - rewrite <- RESV. symmetry. exact (ir_resv _ _ _ IR).
  - exact (c_links X st L BL LS INV).
  - intros h Hh. exact (ch_free _ (c_heads X st L BL LS INV) h Hh).
  - intros g Hm Hn. fold (MR st g) in *. destruct (proj2 (proj1 (il_link _ _ IL g)) Hn) as [h Hh].
    destruct h as [sc|].
    { exfalso. destruct (il_active _ _ IL sc g Hh) as (_ & [b Hb] & _). rewrite (hosts_mem _ _ _ IM _ _ Hb) in Hm. discriminate Hm. }
    pose proof (il_free _ _ IL g Hh) as E. split; [rewrite E; reflexivity|]. split.
    + intros nx Hnx. fold (MR st nx). pose proof (il_free _ _ IL nx (next_listed _ _ _ _ _ INV LFree g nx Hh Hnx)) as E'. rewrite E'. reflexivity.
    + intros pv Hpv. fold (MR st pv). pose proof (il_free _ _ IL pv (prev_listed _ _ _ _ _ INV LFree g pv Hh Hpv)) as E'. rewrite E'. reflexivity.
  - intros q mr Hq. destruct (ia_metas _ IA _ _ Hq) as (a & ar & k & Ha & Hk & Em). exists a, ar, k. auto.
  - unfold ctx. intros NE. destruct (AV ltac:(lia)) as (a & Ht & Hav & FR).
    pose proof (ia_tail _ IA a Ht) as Ha. destruct (s_areas st !! a) as [ar|] eqn:Ea; [| congruence].
    exists a, ar, (NSLOTS - c_avail_meta_count (s_ctx st)). split; [exact Ea|]. split; [exact Hav|]. split; [lia|]. split; [lia|].
    apply FR. lia.
  - unfold ctx. intros tl Ht. pose proof (ia_tail _ IA tl Ht) as Ha. destruct (s_areas st !! tl) as [ar|]; [eexists; reflexivity| congruence].
  - unfold ctx. intros NE. destruct (c_avail_meta_areas (s_ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 ltac:(lia) eq_refl)].
    destruct (C3 rid off eq_refl) as (r & Hr & MK & P1 & P2 & E & _).
    exists (rid, off), r. cbn [fst snd]. split; [reflexivity|]. split; [exact Hr|].
    split; [destruct MK as [K|K]; rewrite K; discriminate|]. split; [exact P2|]. split; [unfold PGSZ in P1; lia|].
    split; [unfold lr_lo; destruct (r_kind r); unfold PGSZ in P1; lia|].
    split; [pose proof (round_up_ge (r_len r)); lia|].
    apply (frontier_fresh rid r off Hr). unfold frontier. rewrite EC, N.eqb_refl. lia.
  - intros q rq Hq. destruct (ir_shape _ _ _ IR _ _ Hq) as (_ & _ & L0 & _). exact L0.
  - pose proof (ir_brk _ _ _ IR) as BR. unfold ctx. destruct (Malloc.c_brk (s_ctx st)) as [| |rid off]; [exact I| exact I|].
    destruct BR as [_ (r & Hr & K & Elen)]. exists r. split; [exact Hr|]. split; [exact K|]. split; [exact Elen|].
    destruct (ir_shape _ _ _ IR _ _ Hr) as (_ & _ & _ & _ & _ & MK). destruct (MK ltac:(left; exact K)) as [M1 M2].
    split; [rewrite <- Elen; exact M1|]. split; [rewrite <- Elen; unfold PGSZ in *; lia|].
    split; [apply (frontier_fresh rid r off Hr); rewrite (ir_brkfront _ _ _ IR _ _ Hr K); lia|].
    intros q rq Hq Kq. exact (ir_brk1 _ _ _ IR _ _ _ _ Hq Hr Kq K).
  - exact (f_ptrs X st L BL LS INV ZB).
Qed.
End GF.

Lemma CORR_GP X st st' L BL LS LB : INVL X st L BL LS -> GP st st' -> CORR st LB BL -> CORR st' LB BL.
Proof.
  intros INV [GPR _] CR. eapply Forall2_impl_in; [exact CR|]. intros b k Hb Hk (C1 & C2 & C3).
  split; [exact C1|]. split; [exact C2|]. rewrite C3. rewrite (conc_same st st' (bslot k)); [reflexivity|].
  destruct (blk_region _ _ _ _ _ k INV Hk) as (r & Hr & Kr). exists r. split; [exact Hr| exact (GPR _ _ Hr Kr)].
Qed.

Definition JINVi (resv : list (Z * Z)) (idle : list aptr) (st : mstate) (LB : list block) : Prop :=
  exists L LS BL, INVL (X_as idle) st L BL LS /\ NoDup idle /\ TF0 st /\ ld_resv L = resv /\ s_secret st = secret_val /\ CORR st LB BL.
Definition JINV (resv : list (Z * Z)) (st : mstate) (LB : list block) : Prop := exists idle, JINVi resv idle st LB.

Lemma jinv_top resv st0 LB t : AREACH_from resv st0 LB -> (s_tick st0 < t)%N -> JINV resv (set_tick t st0) LB.
Proof.
  intros AR Ht. destruct (areach_inv resv st0 LB AR) as (L & LS & BL & INV & _ & RESV & SEC & CR).
  exists [], L, LS, BL. split; [apply INVL_set_tick; [lia| exact INV]|].
  split; [apply NoDup_nil; exact I|| constructor|]. split; [apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| exact Ht]|].
  split; [exact RESV|]. split; [exact SEC|]. exact CR.
Qed.

Lemma jinv_ta resv idle st LB sc st1 :
  JINVi resv idle st LB -> 0 <= sc < 48 -> ta_fail sc st st1 -> JINVi resv idle st1 LB /\ active st1 sc = None.
Proof.
  intros (L & LS & BL & INV & ND & TF & RESV & SEC & CR) Hsc TA.
  destruct (try_avail_ok (option (mstate * Z)) (X_as idle) L BL sc kS bS eq_refl eq_refl Hsc st LS INV) as (st1' & first & LS1 & E & TAF & RES).
  unfold ta_fail in TA. rewrite E in TA. unfold kS in TA. inversion TA. subst st1' first.
  destruct RES as [(_ & HA & INV1)|(g & bg & ai & idx & NZ & _)]; [| exfalso; exact (NZ eq_refl)].
  split; [| exact HA]. exists L, LS1, BL. split; [exact INV1|]. split; [exact ND|].
  split; [exact (TF0_ctrl st st1 (taf_shadow _ _ _ TAF) (taf_tick _ _ _ TAF) TF)|]. split; [exact RESV|].
  split; [rewrite (taf_ssec _ _ _ TAF); exact SEC|]. exact (CORR_GP _ _ _ _ _ _ _ INV (GP_taf _ _ _ TAF) CR).
Qed.

Lemma jinv_am resv idle st1 LB o st2 m :
  JINVi resv idle st1 LB -> leaf_of o (alloc_meta st1 kS bS) (Some (st2, Some m)) -> JINVi resv (m :: idle) st2 LB.
Proof.
  intros (L & LS & BL & INV & ND & TF & RESV & SEC & CR) (ans & o' & FL).
  set (Post := fun (L' : mled) (r : option (mstate * optr)) =>
     match r with
     | Some (s2, Some m') => exists LS', INVL (X_as (m' :: idle)) s2 L' BL LS' /\ ~ In m' idle /\ AM_frame st1 s2 /\ L_frame L L'
     | _ => True
     end).
  assert (FT : ftree L (alloc_meta st1 kS bS) Post).
  { apply (alloc_meta_ft _ BL Post kS bS (X_as idle) st1 L) with (LS := LS); [| | exact INV| apply amf_refl| apply lf_refl].
    - intros s1 L1 LS1 _ _ _. exact I.
    - intros s1 L1 LS1 m' INV1 NI AF LF. cbn. exists LS1. split; [exact INV1|]. split; [exact NI|]. split; [exact AF| exact LF]. }
  pose proof (ftree_prun pans_mem pupd_mem pans_mem_range (alloc_meta st1 kS bS) L Post o FT) as PT.
  unfold mrun in FL. destruct (ptree_follow _ L _ ans PT FL) as (L' & CP & POST). cbn in POST.
  destruct POST as (LS' & INV2 & NI & AF & LF).
  exists L', LS', BL. split; [exact INV2|].
  split; [apply NoDup_cons; split; [intros Hin; apply NI; apply list_elem_of_In; exact Hin| exact ND]|].
  split; [exact (TF0_ctrl st1 st2 (amf_shadow _ _ AF) (amf_tick _ _ AF) TF)|].
  split; [rewrite (lf_resv _ _ LF); exact RESV|].
  split; [rewrite (amf_ssec _ _ AF); exact SEC|]. exact (CORR_GP _ _ _ _ _ _ _ INV (GP_amf _ _ AF) CR).
Qed.

Lemma ist_jinv resv st0 LB st : AREACH_from resv st0 LB -> IST st0 st -> JINV resv st LB.
Proof.
  intros AR. induction 1 as [t Ht|o st sc st1 st2 m _ IH Hsc TA AM].
  - exact (jinv_top resv st0 LB t AR Ht).
  - destruct IH as [idle J]. destruct (jinv_ta _ _ _ _ _ _ J Hsc TA) as [J1 _]. exists (m :: idle). exact (jinv_am _ _ _ _ _ _ _ J1 AM).
Qed.

Lemma jinv_slot resv idle st LB o f sc req st3 idx :
  JINVi resv idle st LB -> 0 <= sc < 48 -> req_ok sc req ->
  leaf_of o (alloc_slot full_lay f st sc req kS bS) (Some (st3, idx)) ->
  exists L LS BL L3 LS3, INVL (X_as idle) st L BL LS /\ SLOT_POST idle sc req st L BL st3 idx L3 LS3
    /\ ld_resv L3 = resv /\ s_secret st3 = secret_val /\ CORR st3 LB BL.
Proof.
  intros (L & LS & BL & INV & ND & TF & RESV & SEC & CR) Hsc [Hreq Hfit] (ans & o' & FL).
  unfold mrun in FL. apply (@alloc_slot_follow_mono _ _ pans_mem pupd_mem full_lay f (f + 49)) in FL; [| lia].
  set (Post := fun (L' : mled) (r : option (mstate * Z)) =>
     match r with Some (s3, i) => exists LS3, SLOT_POST idle sc req st L BL s3 i L' LS3 | None => True end).
  assert (FT : ftree L (alloc_slot full_lay (f + 49) st sc req kS bS) Post).
  { apply (alloc_slot_ft _ Post (f + 49)%nat sc idle st L BL LS req kS bS ltac:(lia) INV TF ND Hsc Hreq Hfit).
    intros st1 i L1 LS1 SP. cbn. exists LS1. exact SP. }
  pose proof (ftree_prun pans_mem pupd_mem pans_mem_range _ L Post o FT) as PT.
  destruct (ptree_follow _ L _ ans PT FL) as (L3 & CP & POST). cbn in POST. destruct POST as [LS3 SP].
  exists L, LS, BL, L3, LS3. split; [exact INV|]. split; [exact SP|].
  split; [rewrite (cpath_resv _ _ _ _ CP); exact RESV|].
  destruct SP as (_ & _ & GP3 & _). split; [rewrite (proj2 GP3); exact SEC|]. exact (CORR_GP _ _ _ _ _ _ _ INV GP3 CR).
Qed.

Theorem ist_facts_proof : forall {resv} st0 LB st, AREACH_from resv st0 LB -> IST st0 st -> @ISTF_g resv st LB.
Proof.
  intros resv st0 LB st AR H. destruct (ist_jinv resv st0 LB st AR H) as (idle & L & LS & BL & INV & ND & TF & RESV & SEC & CR).
  exact (inv_istf (X_as idle) st L BL LS INV eq_refl eq_refl resv LB CR RESV).
Qed.

Theorem istr_facts_proof : forall {resv} st0 LB st3, AREACH_from resv st0 LB -> ISTR st0 st3 -> @ISTF_g resv st3 LB.
Proof.
  intros resv st0 LB st3 AR (o & st & f & sc & req & idx & H & Hsc & RQ & LF).
  destruct (ist_jinv resv st0 LB st AR H) as [idle J].
  destruct (jinv_slot resv idle st LB o f sc req st3 idx J Hsc RQ LF) as (L & LS & BL & L3 & LS3 & INV & SP & RESV & SEC & CR).
  destruct SP as (_ & _ & _ & [(_ & INV3 & _)|(g & bg & ai & _ & _ & _ & _ & _ & _ & INV3 & _)]).
  - exact (inv_istf (X_as idle) st3 L3 BL LS3 INV3 eq_refl eq_refl resv LB CR RESV).
  - exact (inv_istf _ st3 L3 BL LS3 INV3 eq_refl eq_refl resv LB CR RESV).
Qed.

Theorem nest_facts_proof : forall {resv} st0 LB st sc st1 o st2 m f j req o' st3 idx,
  AREACH_from resv st0 LB -> IST st0 st -> 0 <= sc < 48 -> ta_fail sc st st1 ->
  leaf_of o (alloc_meta st1 kS bS) (Some (st2, Some m)) ->
  0 <= j < 48 -> req_ok j req ->
  leaf_of o' (alloc_slot full_lay f st2 j req kS bS) (Some (st3, idx)) ->
  nest_ok m st3.
Proof.
  intros resv st0 LB st sc st1 o st2 m f j req o' st3 idx AR H Hsc TA AM Hj RQ LF.
  destruct (ist_jinv resv st0 LB st AR H) as [idle J].
  destruct (jinv_ta _ _ _ _ _ _ J Hsc TA) as [J1 _]. pose proof (jinv_am _ _ _ _ _ _ _ J1 AM) as J2.
  destruct (jinv_slot resv (m :: idle) st2 LB o' f j req st3 idx J2 Hj RQ LF) as (L & LS & BL & L3 & LS3 & INV & SP & _).
  assert (K : forall X3, INVL X3 st3 L3 BL LS3 -> x_idle X3 = m :: idle -> nest_ok m st3).
  { intros X3 INV3 XI. destruct (im_idle _ _ _ (proj1 (proj2 (proj2 INV3))) m ltac:(rewrite XI; left; reflexivity)) as [Em NI].
    split; [unfold get_meta_rec; rewrite Em; reflexivity|].
    intros h Hh. pose proof (head_listed _ _ _ _ _ INV3 LFree h Hh) as Hin. split.
    - intros ->. apply NI. exists LFree. exact Hin.
    - intros Hp. apply NI. exists LFree. exact (prev_listed _ _ _ _ _ INV3 LFree h m Hin Hp). }
  destruct SP as (_ & _ & _ & [(_ & INV3 & _)|(g & bg & ai & _ & _ & _ & _ & _ & _ & INV3 & _)]).
  - exact (K _ INV3 eq_refl).
  - exact (K _ INV3 eq_refl).
Qed.

Theorem areach_ampre_proof : forall {resv} st LB, AREACH_from resv st LB -> @AMpre_g _ resv st.
Proof.
  intros resv st LB AR. destruct (areach_inv resv st LB AR) as (L & LS & BL & INV & _ & RESV & SEC & _).
  exact (inv_ampre x0 st L BL LS INV eq_refl resv RESV SEC).
Qed.

Theorem ist_ampre_proof : forall {resv}, AMP_AS_g resv (am_pre_g resv).
Proof.
  intros resv st0 LB st sc st1 AR H Hsc TA.
  destruct (ist_jinv resv st0 LB st AR H) as [idle J]. destruct (jinv_ta _ _ _ _ _ _ J Hsc TA) as [(L & LS & BL & INV & _ & _ & RESV & SEC & _) _].
  exact (inv_ampre (X_as idle) st1 L BL LS INV eq_refl resv RESV SEC).
Qed.

Local Definition g1 := (@ist_facts_proof : forall resv st0 LB st, AREACH_from resv st0 LB -> IST st0 st -> @ISTF_g resv st LB).
Local Definition g2 := (@istr_facts_proof : forall resv st0 LB st3, AREACH_from resv st0 LB -> ISTR st0 st3 -> @ISTF_g resv st3 LB).
Local Definition g3 := (@nest_facts_proof : forall resv st0 LB st sc st1 o st2 m f j req o' st3 idx,
  AREACH_from resv st0 LB -> IST st0 st -> 0 <= sc < 48 -> ta_fail sc st st1 ->
  leaf_of o (alloc_meta st1 kS bS) (Some (st2, Some m)) ->
  0 <= j < 48 -> req_ok j req ->
  leaf_of o' (alloc_slot full_lay f st2 j req kS bS) (Some (st3, idx)) ->
  nest_ok m st3).
Local Definition g4 := (@areach_ampre_proof : forall resv st LB, AREACH_from resv st LB -> @AMpre_g _ resv st).
Local Definition g5 := (@ist_ampre_proof : forall resv, AMP_AS_g resv (am_pre_g resv)).
End CEIL_WRAP_1.

