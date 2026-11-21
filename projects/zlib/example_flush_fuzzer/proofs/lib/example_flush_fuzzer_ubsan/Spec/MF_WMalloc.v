(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry MI_WTry2 MI_WGroup MI_Cnt MI_TF2 MI_WCreate2
  MI_WSlot MI_WSlot2 MI_WSlot3 MI_WEnframe MI_WEnframe2 MI_Bits MI_WMalloc MF_Defs MF_WTry MF_WAMeta MF_WSlot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Definition kcls_f (k : Z) : bool :=
  let sc := stc_k k in
  Bool.eqb (sc =? 30) ((340 <=? k) && (k <=? 408)) && Bool.eqb (sc =? 31) ((409 <=? k) && (k <=? 510))
  && Bool.eqb (sc =? 40) ((2047 <=? k) && (k <=? 2339)) && Bool.eqb (sc =? 44) ((4095 <=? k) && (k <=? 4679)).
Lemma kcls_b_true : forallb kcls_f (zrange 0 8191) = true. Proof. vm_compute. reflexivity. Qed.

Lemma size_to_class_K n : 0 <= n < MMAP_THRESHOLD ->
  let sc := size_to_class n in
  (sc = 30 <-> 5437 <= n <= 6540) /\ (sc = 31 <-> 6541 <= n <= 8172) /\ (sc = 40 <-> 32749 <= n <= 37436) /\ (sc = 44 <-> 65517 <= n <= 74876).
Proof.
  intros Hn. cbn zeta. rewrite size_to_class_k. rewrite Z.shiftr_div_pow2 by lia. unfold IB, MMAP_THRESHOLD in *.
  set (k := (n + 4 - 1) / 2 ^ 4).
  assert (Hk : 0 <= k < 8191) by (subst k; change (2 ^ 4) with 16; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (Hk2 : 16 * k <= n + 3 < 16 * k + 16) by (subst k; change (2 ^ 4) with 16; pose proof (Z.div_mod (n + 4 - 1) 16 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 4 - 1) 16 ltac:(lia)); lia).
  pose proof (forallb_zrange kcls_f 0 8191 k kcls_b_true ltac:(lia) ltac:(lia)) as H. unfold kcls_f in H. cbn zeta in H.
  apply andb_true_iff in H as [H H44]. apply andb_true_iff in H as [H H40]. apply andb_true_iff in H as [H30 H31].
  apply Bool.eqb_prop in H30. apply Bool.eqb_prop in H31. apply Bool.eqb_prop in H40. apply Bool.eqb_prop in H44.
  assert (R : forall c lo hi, (stc_k k =? c) = ((lo <=? k) && (k <=? hi)) -> (stc_k k = c <-> lo <= k <= hi)).
  { intros c lo hi E. destruct (Z.eqb_spec (stc_k k) c); destruct (Z.leb_spec lo k); destruct (Z.leb_spec k hi); cbn in E; try discriminate; split; intros; lia. }
  pose proof (R _ _ _ H30) as R30. pose proof (R _ _ _ H31) as R31. pose proof (R _ _ _ H40) as R40. pose proof (R _ _ _ H44) as R44.
  clear R H30 H31 H40 H44. repeat split; intros; lia.
Qed.


Definition csel (st : mstate) (n : Z) : Z :=
  let sc := size_to_class n in
  match active st sc with
  | Some _ => sc
  | None =>
    if (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) then
      let usage1 := usage st (Z.lor sc 1) in
      let usage1 := match active st (Z.lor sc 1) with
                    | None => usage1 + 3
                    | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
                                if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
                    end in
      if usage1 <=? 12 then Z.lor sc 1 else sc
    else sc
  end.

Lemma csel_cases st n : csel st n = size_to_class n \/ (csel st n = size_to_class n + 1 /\ Z.even (size_to_class n) = true /\ 4 <= size_to_class n < 32).
Proof.
  unfold csel. set (sc := size_to_class n). destruct (active st sc); [left; reflexivity|].
  destruct ((4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0)) eqn:E; [| left; reflexivity].
  match goal with |- context [if ?c then Z.lor sc 1 else sc] => destruct c end; [| left; reflexivity].
  apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2. right. rewrite (lor1_even sc ltac:(lia) EV). auto.
Qed.


Definition CORE_POSTF (st0 : mstate) (n : Z) (L : mled) (BL : list blk) (L1 : mled) (r : mstate * option (aptr * Z)) : Prop :=
  ld_live L1 = ld_live L /\
  (n < MMAP_THRESHOLD -> MFR (csel st0 n) st0 (fst r)) /\ (MMAP_THRESHOLD <= n -> MFR 63 st0 (fst r)) /\
  match snd r with
  | None => exists LS1, INVL x0 (fst r) L1 BL LS1
  | Some (g, idx) => exists LS1 bg, let st1 := fst r in
      hosts st1 bg g /\ 0 <= idx <= m_last_idx (MR st1 g)
      /\ INVL (xpend x0 (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1
      /\ n + IB <= get_stride (MR st1 g) /\ TF2 st1 /\ get_stride (MR st1 g) - IB - n < 2 ^ 32
      /\ (n < MMAP_THRESHOLD -> m_sizeclass (MR st1 g) = csel st0 n /\ XNEW (csel st0 n) n st0 st1 g bg)
  end.

Section CORE.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (n : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis TF : TF0 st.
Hypothesis Hn : 0 <= n.

Lemma malloc_small_ftF : n < MMAP_THRESHOLD ->
  ftree L (malloc_small_ctrl full_lay st n (fun st1 r => ret (st1, r)) (ret (st, @None (aptr * Z)))) (CORE_POSTF st n L BL).
Proof.
  intros Hlt. pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT].
  unfold malloc_small_ctrl.
  set (sc0 := size_to_class n) in *.
  set (sc := match active st sc0 with Some _ => sc0 | None => _ end).
  assert (Esc : sc = csel st n) by reflexivity.
  assert (SC' : 0 <= sc < 48 /\ n + IB <= UNIT * size_class sc).
  { rewrite Esc. destruct (csel_cases st n) as [E|(E & EV & R)]; rewrite E; fold sc0; [auto|].
    split; [lia|]. pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). unfold UNIT in *. lia. }
  clearbody sc. destruct SC' as [SC' FIT'].
  assert (SLOT : ftree L (alloc_slot full_lay FUEL st sc n (fun st1 idx =>
              if idx <? 0 then ret (st1, None) else match active st1 sc with Some gp => ret (st1, Some (gp, idx)) | None => SVis (EUndef UBadPtr) (fun _ => ret (st, None)) end)
              (ret (st, None))) (CORE_POSTF st n L BL)).
  { apply (alloc_slot_ftF (mstate * option (aptr * Z)) (CORE_POSTF st n L BL) FUEL sc [] st L BL LS n); try assumption.
    * unfold FUEL. cbn. lia.
    * apply NoDup_nil_2.
    * intros st1 idx L1 LS1 (ACT & LIVE & MF1 & RES). destruct RES as [(-> & INV1 & TF1)|(g & bg & ai & Hidx & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1 & XN1)].
      -- cbn [ftree ret]. unfold CORE_POSTF. cbn [fst snd]. split; [exact LIVE|]. split; [intros _; rewrite <- Esc; exact MF1|]. split; [intros; lia|]. exists LS1. exact INV1.
      -- replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1. cbn [ftree ret]. unfold CORE_POSTF. cbn [fst snd]. split; [exact LIVE|].
         split; [intros _; rewrite <- Esc; exact MF1|]. split; [intros; lia|].
         exists LS1, bg. split; [exists ai; exact Hg|]. split; [exact Hidx|]. split; [exact INV1|]. split; [exact FIT1|]. split; [exact TF1|].
         split; [pose proof (small_stride _ _ _ _ _ bg g INV1 (ex_intro _ ai Hg) ltac:(lia)); unfold IB; lia|].
         intros _. rewrite <- Esc. split; [exact SCg| exact XN1]. }
  destruct (active st sc) as [gp|] eqn:HA.
  -
    destruct (Z.eqb_spec (m_avail (get_meta_rec st gp)) 0) as [AZ|ANZ].
    + rewrite AZ. change (lowbit 0) with 0. cbn [negb Z.eqb]. exact SLOT.
    +
      destruct (hd_facts x0 st L BL LS sc gp INV HA) as (_ & Egp & bm & ai & Hbm).
      pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbm) as GO.
      pose proof (proj1 (g_masks _ _ _ _ _ _ GO)) as A0. fold (MR st gp) in ANZ |- *.
      destruct (lowbit_idiom (m_avail (MR st gp)) ltac:(lia)) as (k & Hk & LB & CTZ & TB & _).
      assert (LNZ : (lowbit (m_avail (MR st gp)) =? 0) = false) by (apply Z.eqb_neq; rewrite LB; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); lia).
      rewrite LNZ. cbn [negb ftree ret]. unfold CORE_POSTF. cbn [fst snd]. split; [reflexivity|].
      pose proof (ta_fin_ok x0 st L BL LS gp bm ai INV eq_refl eq_refl Hbm ltac:(rewrite Egp; exact (hd_head x0 st L BL LS sc gp INV HA)) ANZ) as (INV1 & Hidx & _ & _ & STR).
      set (st1 := upd_meta gp (m_set_avail (m_avail (MR st gp) - lowbit (m_avail (MR st gp)))) st) in *.
      assert (MF01 : MF0 st st1).
      { apply MF0_of; [intros b h Hb; exists h; auto| intros x; unfold st1, MR; destruct (aptr_eq_dec x gp) as [->|NE]; [rewrite get_meta_rec_upd_same; apply same_geo_set_avail| rewrite get_meta_rec_upd_other by exact NE; apply same_geo_refl]| unfold st1, bounces, ctx; cbn [s_ctx upd_meta put_meta Malloc.set_metas]; lia]. }
      split; [intros _; rewrite <- Esc; exact (MF0_MFR sc _ _ MF01)|]. split; [intros; lia|].
      assert (MR1 : forall x, x <> gp -> MR st1 x = MR st x) by (intros x NE; unfold st1, MR; apply get_meta_rec_upd_other; exact NE).
      assert (MRg : m_last_idx (MR st1 gp) = m_last_idx (MR st gp) /\ get_stride (MR st1 gp) = get_stride (MR st gp) /\ (forall i, sstart (MR st1 gp) i = sstart (MR st gp) i) /\ m_sizeclass (MR st1 gp) = m_sizeclass (MR st gp)).
      { unfold st1, MR. rewrite get_meta_rec_upd_same. destruct (get_meta_rec st gp); cbn; repeat split; reflexivity. }
      destruct MRg as (ML & MS & MSS & MSC).
      exists LS, bm. rewrite ML, MS, MSS. split; [exists ai; exact Hbm|]. split; [exact Hidx|]. split; [exact INV1|].
      rewrite Egp in STR. split; [lia|].
      split; [apply TF0_TF2; apply (TF0_ctrl st st1); [reflexivity| reflexivity| exact TF]|].
      split; [pose proof (small_stride _ _ _ _ _ bm gp INV (ex_intro _ ai Hbm) ltac:(lia)); unfold IB; lia|].
      intros _. rewrite <- Esc. split; [rewrite MSC; exact Egp|].
      intros _ _ _. left. split; [exists ai; exact Hbm| unfold st1, MR; rewrite get_meta_rec_upd_same; apply same_geo_set_avail].
  -
    change (lowbit 0) with 0. cbn [negb Z.eqb]. exact SLOT.
Qed.

Lemma malloc_big_ftF : MMAP_THRESHOLD <= n -> size_overflows n = false ->
  ftree L
    (SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
      if negb (mmap_answer_ok (s_atop st) (live_ranges st) (n + IB + UNIT) r) then bad_answer (ret (st, @None (aptr * Z))) else
      if is_err r then ret (st, None) else
      let '(st1, rid) := new_region RKGroup r (n + IB + UNIT) st in
      let st2 := step_seq st1 in
      alloc_meta st2 (fun st3 go =>
        match go with
        | None => SVis (EMunmap r (n + IB + UNIT)) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, @None (aptr * Z)) else bad_answer (ret (st, @None (aptr * Z))))
        | Some g =>
          let st4 := upd_meta g (fun mr => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((n + IB + UNIT + 4095) / 4096)
                       (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
          let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) (lh_hdr full_lay st4 (rid, 0)) in
          let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
          let st7 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6 in
          ret (st7, Some (g, 0))
        end) (ret (st, @None (aptr * Z)))))
    (CORE_POSTF st n L BL).
Proof.
  intros Hbig Hov. unfold size_overflows in Hov. apply Z.leb_gt in Hov.
  set (needed := n + IB + UNIT).
  assert (HN : 131072 <= needed < 2 ^ 63 - 4000) by (unfold needed, IB, UNIT, MMAP_THRESHOLD in *; lia).
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  apply ftree_vis; [reflexivity| reflexivity| | |].
  - cbn. left. split; [exact (brk_quiet_of _ _ _ IR)|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity|].
    unfold LEN_MAX. clear -HN. lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    change (event_post L (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) a)
      with (if Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0 then if is_err a then L else if PROT_RW =? PROT_NONE then KInv.set_metas ((a, needed, 0) :: ld_metas L) L else KInv.set_groups ((a, needed) :: ld_groups L) L else set_brkph BPLive (set_brkreg (Some (0, 2 * PGSZ)) L)).
    change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_RW =? PROT_NONE) with false. cbn iota.
    rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. cbn [negb].
    destruct (is_err a) eqn:ER.
    + cbn [ftree ret]. unfold CORE_POSTF. cbn [fst snd]. split; [reflexivity|]. split; [intros; lia|]. split; [intros _; apply MFR_refl|]. exists LS. exact INV.
    + destruct (new_region RKGroup a needed st) as [st1 rid] eqn:EN.
      assert (Erid : rid = s_next_rid st) by (unfold new_region in EN; inversion EN; reflexivity).
      assert (Est1 : st1 = fst (new_region RKGroup a needed st)) by (rewrite EN; reflexivity).
      pose proof (INVL_new_group_region x0 st L BL LS a needed INV eq_refl Ha ER ltac:(unfold LEN_MAX; clear -HN; lia)) as INV1.
      rewrite <- Est1, <- Erid in INV1.
      set (L1 := KInv.set_groups ((a, needed) :: ld_groups L) L) in *.
      assert (Hr1 : s_regions st1 !! rid = Some (mkRegion RKGroup a needed)) by (rewrite Est1, ng_lookup, Erid, N.eqb_refl; reflexivity).
      assert (NS1 : s_shadow st1 !! rid = None).
      { rewrite Est1, Erid. change (s_shadow (fst (new_region RKGroup a needed st))) with (s_shadow st). exact (shadow_next_rid_none _ _ _ _ _ INV). }
      assert (TF1 : TF0 (step_seq st1)).
      { destruct (step_seq_fields st1) as (A & B & _). apply (TF0_ctrl st1); [exact A| exact B|]. apply (TF0_ctrl st); [rewrite Est1; reflexivity| rewrite Est1; reflexivity| exact TF]. }
      pose proof (INVL_step_seq _ _ _ _ _ INV1) as INV2.
      destruct (step_seq_fields st1) as (SS1 & SS2 & SS3 & SS4 & SS5 & SS6 & SS7 & _).
      assert (MF02 : MF0 st (step_seq st1)).
      { apply MF0_eq; [rewrite SS7, Est1; reflexivity| rewrite SS6, Est1; reflexivity| unfold step_seq; destruct (_ =? 255); rewrite Est1; reflexivity]. }
      eapply (alloc_meta_ftG (mstate * option (aptr * Z)) BL (CORE_POSTF st n L BL) _ _ (xorph x0 (Some rid)) (step_seq st1) L1);
        [ | | exact INV2| apply amf_refl| apply GEQ_refl| apply lf_refl].
      *
        intros st3 L3 LS3 INV3 AF GE LF. cbn beta iota.
        assert (MF03 : MF0 st st3).
        { eapply MF0_trans; [exact MF02|]. apply MF0_of; [intros b h Hb; rewrite (amf_groups _ _ AF) in Hb; exists h; auto| exact GE| unfold bounces, ctx; rewrite (amf_bounces _ _ AF); lia]. }
        apply ftree_vis; [reflexivity| reflexivity| | |].
        -- cbn. split; [exact (brk_quiet_of _ _ _ (proj1 INV3))|]. exists needed. rewrite (lf_groups _ _ LF). split; [left; reflexivity| left; reflexivity].
        -- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. cbn [ftree ret]. unfold CORE_POSTF. cbn [fst snd event_post].
           split; [cbn; rewrite (lf_live _ _ LF); reflexivity|].
           split; [intros; lia|]. split; [intros _; apply MF0_MFR; eapply MF0_trans; [exact MF03| apply MF0_eq; reflexivity]|].
           exists LS3.
           pose proof (INVL_drop_orph (xorph x0 (Some rid)) st3 L3 BL LS3 rid (mkRegion RKGroup a needed) INV3 eq_refl
                         (amf_regions _ _ AF rid _ ltac:(rewrite SS4; exact Hr1) eq_refl)) as INV4.
           cbn [r_base xorph x_idle x_zomb x_pend x_fresh x_orph] in INV4. exact INV4.
        -- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. exact I.
      *
        intros st3 L3 LS3 g INV3 NIg AF GE LF. cbn beta iota zeta.
        assert (MF03 : MF0 st st3).
        { eapply MF0_trans; [exact MF02|]. apply MF0_of; [intros b h Hb; rewrite (amf_groups _ _ AF) in Hb; exists h; auto| exact GE| unfold bounces, ctx; rewrite (amf_bounces _ _ AF); lia]. }
        change (lh_hdr full_lay) with (fun s b => hdr_havoc b s). cbn beta.
        assert (Hr3 : s_regions st3 !! rid = Some (mkRegion RKGroup a needed)) by (apply (amf_regions _ _ AF); [rewrite SS4; exact Hr1| reflexivity]).
        assert (NS3 : s_shadow st3 !! rid = None) by (rewrite (amf_shadow _ _ AF), SS1; exact NS1).
        assert (TF3 : TF0 st3) by (apply (TF0_ctrl (step_seq st1)); [exact (amf_shadow _ _ AF)| exact (amf_tick _ _ AF)| exact TF1]).
        cbn [xidle xorph x_idle x_zomb x_pend x_orph x_fresh x0] in INV3.
        destruct (create63_ok st3 L3 BL LS3 g rid (mkRegion RKGroup a needed) needed INV3 Hr3 eq_refl eq_refl NS3 ltac:(lia) TF3)
          as (INV6 & TF6 & MR6 & GR6 & CTX6 & TK6 & RG6 & STR6 & RU6).
        match goal with |- ftree _ (ret (upd_ctx ?f ?s6, _)) _ => set (st6 := s6) in * end.
        cbn [ftree ret]. unfold CORE_POSTF. cbn [fst snd]. split; [cbn; exact (lf_live _ _ LF)|].
        assert (SG3 : s_groups st3 = s_groups st).
        { rewrite (amf_groups _ _ AF). rewrite SS7, Est1. reflexivity. }
        pose proof (INVL_mmap_counter _ _ _ _ _ INV6) as INV7.
        set (st7 := upd_ctx _ st6) in *.
        assert (MR7 : MR st7 g = MR st6 g) by reflexivity.
        assert (GRX : s_groups st7 = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3)).
        { change (s_groups st7) with (s_groups st6). apply map_eq. intros b. destruct (decide (b = (rid, 0))) as [->|NE]; [rewrite lookup_insert_eq; exact GR6|].
          rewrite lookup_insert_ne by congruence. change (s_groups st6) with (s_groups (put_group (rid, 0) (Some g)
             (group_active_idx (upd_meta g (fun mr => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096) (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3) (rid, 0))
             (hdr_havoc (rid, 0) (upd_meta g (fun mr => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096) (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3)))).
          unfold put_group. cbn [s_groups Malloc.set_groups hdr_havoc upd_shadow upd_meta put_meta Malloc.set_metas]. rewrite lookup_insert_ne by congruence. reflexivity. }
        assert (MRo : forall x, x <> g -> MR st7 x = MR st3 x).
        { intros x NE. change (MR st7 x) with (MR st6 x). unfold MR, get_meta_rec.
          change (s_metas st6) with (s_metas (upd_meta g (fun mr => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096) (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3)).
          rewrite s_metas_upd_meta, lookup_insert_ne by congruence. reflexivity. }
        split; [intros; lia|].
        split.
        { intros _. apply (MFR_MF0_l 63 _ _ _ MF03). constructor.
          - intros b m ai Hb. rewrite GRX in Hb. destruct (decide (b = (rid, 0))) as [->|NE].
            + rewrite lookup_insert_eq in Hb. inversion Hb. subst m. right. left. rewrite MR7, MR6. reflexivity.
            + rewrite lookup_insert_ne in Hb by congruence. left. split; [exists ai; exact Hb|].
              assert (NEg : m <> g) by (intros ->; exact (idle_not_gmeta _ st3 L3 BL LS3 g b ai INV3 ltac:(cbn; left; reflexivity) Hb)).
              rewrite (MRo m NEg). apply same_geo_refl.
          - intros _. change (bounces st7 24) with (bounces st6 24). unfold bounces, ctx. rewrite CTX6. cbn. lia. }
        exists LS3, (rid, 0). rewrite MR7, MR6. cbn [m_last_idx].
        assert (SS0 : sstart (mkMeta None None (Some (rid, 0)) 0 0 0 1 63 ((needed + 4095) / 4096)) 0 = 16).
        { unfold sstart, gbase. cbn -[Z.mul Z.add get_stride]. unfold UNIT. lia. }
        rewrite SS0. change (fst (rid, 0)) with rid.
        split; [exists 0; exact GR6|]. split; [lia|]. split; [exact INV7|].
        rewrite STR6. pose proof (round_up_pg_spec needed) as [RU _].
        unfold needed, IB, UNIT in *.
        split; [lia|]. split; [apply TF0_TF2; apply (TF0_ctrl st6); [reflexivity| reflexivity| exact TF6]|]. split; [lia|].
        intros; lia.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. exact I.
Qed.

Theorem malloc_core_ftF : ftree L (malloc_core full_lay st n) (CORE_POSTF st n L BL).
Proof.
  unfold malloc_core.
  destruct (size_overflows n) eqn:Hov.
  - cbn [ftree ret]. unfold CORE_POSTF. cbn [fst snd]. split; [reflexivity|]. split; [intros _; apply MFR_refl|]. split; [intros _; apply MFR_refl|]. exists LS. exact INV.
  - destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hbig|Hsmall].
    + exact (malloc_big_ftF Hbig Hov).
    + exact (malloc_small_ftF Hsmall).
Qed.
End CORE.



