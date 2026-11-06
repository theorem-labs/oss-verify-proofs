(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow
  MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry MI_WTry2 MI_WGroup MI_Cnt MI_TF2 MI_WCreate2
  MI_WSlot MI_WSlot2 MI_WSlot3 MI_WEnframe MI_WEnframe2 MI_Bits.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~he4INVL37Corelib7Numbers7BinNumsm31N79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~o04mledhe3blkhe6extras79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~t24aptrt25lheadt26mstatet26s_tickt28set_tick46Stdlib6NArith6BinNat1Nhjc2le04prodm31Z06option37Corelib4Init5Logichmc3andt26region03fsthmc2eqhe2MRhmc2ext22IB46Stdlib6ZArith6BinInt1Zhqb3addhqb2le04Someo07ld_livehe2x0t2aget_stridehqb3sub25stdpp9countablehv9bN_countable35stdpp7numbers1Nih96eq_dec04pair03sndhe5hostshe6sstart79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_TF2~~~~~~il03TF279OSSVerify6Proofsaboost_jsonafuzz_parse3lib4SpecaMI_WAMeta2~~~~~~ip55AREAS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec9MI_WFree2~~~~~~iu05xpend79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec8MI_WSlot~~~~~~jia2GPt24FUELt27RKGroupt24UNITt24cptrt2am_last_idxt2bm_sizeclasst26r_kindt25r_lent25rkindt29s_regionshqb2lthqb3pow25stdpp4basejtc6lookup25stdpp4gmapjv24gmapjv2bgmap_lookupt23ret04None79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7MI_Tree~~~~~~ki15ftree79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4SpecaMI_WMalloc~~~~~~km99CORE_POSTt2eMMAP_THRESHOLDt28full_layt2h1malloc_small_ctrlt2bmalloc_coret24optr04conshmc3not37Corelib5Lists7ListDeflgb3maphe5bslott24aaddt26malloc36Stdlib5Lists4Listlk12Inhqb3mulil03TF0" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma INVL_set_tick : ltac2:(zQ "c0!h8!lc!nc!rc!s3!s9!hh0!hh7!hhf!hi8!hj1!hl4>1X$5>2st$8>1L$3>2BL@1$0$4>2LS>0$7@1$0$6>1t$2>0@2$b@1$9^5^1>0@5$1^7^6^5^4^3@5$1^8@2$a^3^7^6^5^4").
Proof. intros X st L BL LS t.
  intros Ht (IR & IA & IM & IL & IG & IS & ISH).
  assert (CE : ctrl_eq st (set_tick t st)) by (constructor; reflexivity).
  split; [apply (inv_R_ctrl X st _ L CE); exact IR|]. split; [apply (inv_A_ctrl st _ CE); exact IA|].
  split; [apply (inv_M_ctrl X st _ LS CE); exact IM|]. split; [apply (inv_L_ctrl st _ LS CE); exact IL|].
  split; [apply (inv_G_ctrl X st _ LS CE); exact IG|]. split; [apply (inv_S_ctrl X st _ BL CE); exact IS|].
  apply inv_SH_set_tick; [exact Ht| exact ISH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition CORE_POST : ltac2:(zQ "80!hla!hm0!rc!hhf!h8!hm4!s3!hh0>3st0$3>1n$1>1L$2>2BL@1$4$6>2L1$2>1r@2$0$3@1$5@2$0$7$1P") := ltac2:(zQ "j20!hm0!hh0!hla!ho0!hm4!hhf!nc!ho7!hp0!h8!hp5!hpb!hq0!hh7!hq6!hs3!hsa!ht0!ht6!rc!lc!hu0!hu5!hv2!iga!iia!ij4!ija!s3!ijf!ik7!ioe!it7!ji1!jma!jn0!jn7!jo1!jo8!jof!jpc!jqa!jr3!jrb!js3!jsf!jt5!ju8!jve!kg6\3st0$5\1n$0\1L$h3\2BL@1$9$hc\2L1$h3\1r@2$2$5@1$4@2$2$1$0@2$3@3$a@1$9$i6@1$h2^2@1$h2^4@2$3@2$i2^6@3$8$5@1$4@2$2$1$0^1@2$3@4$i0$i3^3^6@3$8$5@1$4@2$2$1$0^1M4\1x@1$4@2$2$1$0P@3$hb$5@1$4@2$2$1$0^1\1p@2$2$1$0M2\1p@2$2$1$0P^1\1g$1\3idx$0@2$c>0$d@1$9$1\3LS1>0$d@1$9$1@2$c$1\2bg$1=3st1$5@3$8$5@1$4@2$2$1$0^6@2$3@3$hd^1^2^5@2$3@2$3@2$h0Z^4@2$h0^4@1$i7@2$b^1^5@2$3@5$h4@2$i1$h5@2$h1@2$2$6$0@4$ha$6$0@3$8$6$0^2@2$he@2$b^1^5^4^1^8^9^3@2$3@2$h0@2$f^b$e@1$h6@2$b^1^5@2$3@1$hf^1@2$3@2$id@2$h7@2$h7@1$h6@2$b^1^5$e^b@2$ie+2+i0>0@3$a$0@1$i8@2$b^1^5+jf@2$c$7\2rg$7@2$3@3$a@1$4$7@6$if$6$7@4$j0$6$h9$h8$7@4$j1$6$h9$h8$7@3$8$6$0^4@1$ic^3@2$h1$7^1@2$3@3$a$ib@1$i9^1$i4@3$a$0@1$ia^1@2$f@2$f^d$e$i5@2$c>0$d@1$9$1\3LS1>0$d@1$9$1@5$h4$h5@3$8$5@1$4@2$2$1$0^2^3^4^1").

Lemma small_stride : ltac2:(zQ "e0!hh0!h8!hpb!jsf!rc!lc!s3!s9!ijf!hu5!hh7!jpc!hhf!jt5>1X$7>2st$c>1L$4>2BL@1$1$6>2LS>0$a@1$1$0>2bg$0>1g$0>0@5$5^7^6^5^4^3>0@3$8^7^3^2>0@2$3@1$b@2$2^8^3+j0@2$3@1$9@2$2^9^4@2$d+2+h4").
Proof. intros X st L BL LS bg g.
  intros INV [ai Hb] Hsc. pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hb) as GO.
  destruct (g_stride _ _ _ _ _ _ GO Hsc) as (_ & _ & LT). pose proof (g_li _ _ _ _ _ _ GO). unfold cnt_of in LT.
  pose proof (stride_ge _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ (ex_intro _ ai Hb)) as [S _]. unfold UNIT in S. nia.
Qed.

Section CORE.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (n : Z).
Hypothesis INV : ltac2:(zQ "20!lc!hu0@5$0$1?2st?1L?2BL?2LS").
Hypothesis TF : ltac2:(zQ "10!lm1@1$0?2st").
Hypothesis Hn : ltac2:(zQ "10!hsa@2$0Z?1n").

(* [comment removed for export] *)
Lemma malloc_small_ft : ltac2:(zQ "e0!hla!hm0!hh0!hm4!hhf!ij4!kh5!khb!km0!kqb!kr8!ks9!kt4!jsf>0@2$d?1n$a@4$8@2$0$4@1$3@2$0$2$1?1L@6$c@2$0$4@1$3@2$0$2$1$b?2st?1n\3st1$4\1r@1$3@2$0$2$1@2$6@2$0$4@1$3@2$0$2$1@4$5$4@1$3@2$0$2$1^2^1@2$6@2$0$4@1$3@2$0$2$1@4$5$4@1$3@2$0$2$1?2st@1$7@2$0$2$1@4$9?2st?1n?1L?2BL").
Proof.
  intros Hlt. pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT].
  unfold malloc_small_ctrl.
  set (sc0 := size_to_class n) in *.
  set (sc := match active st sc0 with Some _ => sc0 | None => _ end).
  assert (SC' : 0 <= sc < 48 /\ n + IB <= UNIT * size_class sc).
  { subst sc. destruct (active st sc0); [auto|].
    destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0)) eqn:E; [| auto].
    match goal with |- context [if ?c then Z.lor sc0 1 else sc0] => destruct c end; [| auto].
    apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    rewrite (lor1_even sc0 ltac:(lia) EV). split; [lia|].
    pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). unfold UNIT in *. lia. }
  clearbody sc. destruct SC' as [SC' FIT'].
  destruct (active st sc) as [gp|] eqn:HA.
  - (* [comment removed for export] *)
    destruct (Z.eqb_spec (m_avail (get_meta_rec st gp)) 0) as [AZ|ANZ].
    + rewrite AZ. change (lowbit 0) with 0. cbn [negb Z.eqb].
      (* [comment removed for export] *)
      apply (alloc_slot_ft (mstate * option (aptr * Z)) (CORE_POST st n L BL) FUEL FUEL sc [] st L BL LS n); try assumption.
      * unfold FUEL. cbn. lia.
      * apply NoDup_nil_2.
      * cbn. lia.
      * intros st1 idx L1 LS1 (ACT & LIVE & GP1 & AR1 & RES). destruct RES as [(-> & INV1 & TF1)|(g & bg & ai & Hidx & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1)].
        -- cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|]. split; [exact AR1|]. exists LS1. exact INV1.
        -- replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1. cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|]. split; [exact AR1|].
           exists LS1, bg. split; [exists ai; exact Hg|]. split; [exact Hidx|]. split; [exact INV1|]. split; [exact FIT1|]. split; [exact TF1|].
           split; [| intros E63; exfalso; lia].
           pose proof (small_stride _ _ _ _ _ bg g INV1 (ex_intro _ ai Hg) ltac:(lia)). unfold IB. lia.
    + (* [comment removed for export] *)
      destruct (hd_facts x0 st L BL LS sc gp INV HA) as (_ & Esc & bm & ai & Hbm).
      pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbm) as GO.
      pose proof (proj1 (g_masks _ _ _ _ _ _ GO)) as A0. fold (MR st gp) in ANZ |- *.
      destruct (lowbit_idiom (m_avail (MR st gp)) ltac:(lia)) as (k & Hk & LB & CTZ & TB & _).
      assert (LNZ : (lowbit (m_avail (MR st gp)) =? 0) = false) by (apply Z.eqb_neq; rewrite LB; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); lia).
      rewrite LNZ. cbn [negb ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [reflexivity|]. split; [apply GP_eq; reflexivity|]. split; [apply AREAS_eq; reflexivity|].
      pose proof (ta_fin_ok x0 st L BL LS gp bm ai INV eq_refl eq_refl Hbm ltac:(rewrite Esc; exact (hd_head x0 st L BL LS sc gp INV HA)) ANZ) as (INV1 & Hidx & _ & _ & STR).
      set (st1 := upd_meta gp (m_set_avail (m_avail (MR st gp) - lowbit (m_avail (MR st gp)))) st) in *.
      assert (MR1 : forall x, x <> gp -> MR st1 x = MR st x) by (intros x NE; unfold st1, MR; apply get_meta_rec_upd_other; exact NE).
      assert (MRg : m_last_idx (MR st1 gp) = m_last_idx (MR st gp) /\ get_stride (MR st1 gp) = get_stride (MR st gp) /\ (forall i, sstart (MR st1 gp) i = sstart (MR st gp) i) /\ m_sizeclass (MR st1 gp) = m_sizeclass (MR st gp)).
      { unfold st1, MR. rewrite get_meta_rec_upd_same. destruct (get_meta_rec st gp); cbn; repeat split; reflexivity. }
      destruct MRg as (ML & MS & MSS & MSC).
      exists LS, bm. rewrite ML, MS, MSS. split; [exists ai; exact Hbm|]. split; [exact Hidx|]. split; [exact INV1|].
      rewrite Esc in STR. split; [lia|].
      split; [apply TF0_TF2; apply (TF0_ctrl st st1); [reflexivity| reflexivity| exact TF]|].
      rewrite MSC. split; [| intros E63; exfalso; lia].
      pose proof (small_stride _ _ _ _ _ bm gp INV (ex_intro _ ai Hbm) ltac:(lia)). unfold IB. lia.
  - (* [comment removed for export] *)
    change (lowbit 0) with 0. cbn [negb Z.eqb].
    apply (alloc_slot_ft (mstate * option (aptr * Z)) (CORE_POST st n L BL) FUEL FUEL sc [] st L BL LS n); try assumption.
    + unfold FUEL. cbn. lia.
    + apply NoDup_nil_2.
    + cbn. lia.
    + intros st1 idx L1 LS1 (ACT & LIVE & GP1 & AR1 & RES). destruct RES as [(-> & INV1 & TF1)|(g & bg & ai & Hidx & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1)].
      * cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|]. split; [exact AR1|]. exists LS1. exact INV1.
      * replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1. cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|]. split; [exact AR1|].
        exists LS1, bg. split; [exists ai; exact Hg|]. split; [exact Hidx|]. split; [exact INV1|]. split; [exact FIT1|]. split; [exact TF1|].
        pose proof (small_stride _ _ _ _ _ bg g INV1 (ex_intro _ ai Hg) ltac:(lia)). unfold IB. lia.
Qed.

(* [comment removed for export] *)
Lemma malloc_big_ft : MMAP_THRESHOLD <= n -> size_overflows n = false ->
  ftree L
    (SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
      if negb (mmap_answer_ok (live_ranges st) (n + IB + UNIT) r) then bad_answer (ret (st, @None (aptr * Z))) else
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
    (CORE_POST st n L BL).
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
    + cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [reflexivity|]. split; [apply GP_refl|]. split; [apply AREAS_refl|]. exists LS. exact INV.
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
      destruct (step_seq_fields st1) as (SS1 & SS2 & SS3 & SS4 & SS5 & _).
      eapply (alloc_meta_ft (mstate * option (aptr * Z)) BL (CORE_POST st n L BL) _ _ (xorph x0 (Some rid)) (step_seq st1) L1 FUEL);
        [reflexivity| cbn; lia| reflexivity| reflexivity | | | exact INV2| apply amf_refl| apply lf_refl| apply AREAS_refl].
      * (* [comment removed for export] *)
        intros st3 L3 LS3 INV3 AF LF AR3. cbn beta iota.
        apply ftree_vis; [reflexivity| reflexivity| | |].
        -- cbn. split; [exact (brk_quiet_of _ _ _ (proj1 INV3))|]. exists needed. rewrite (lf_groups _ _ LF). split; [left; reflexivity| left; reflexivity].
        -- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. cbn [ftree ret]. unfold CORE_POST. cbn [fst snd event_post].
           split; [cbn; rewrite (lf_live _ _ LF); reflexivity|].
           split.
           { split.
             - intros q rq Hq Kq. unfold drop_region. rewrite s_regions_set_shadow, s_regions_set_regions. rewrite lookup_delete_ne.
               + apply (amf_regions _ _ AF); [| exact Kq]. rewrite SS4, Est1. apply (ng_keep _ _ _ _ _ _ _ INV). exact Hq.
               + intros ->. pose proof (ir_ids _ _ _ (proj1 INV) _ _ Hq). rewrite Erid in H. lia.
             - transitivity (s_secret st3); [reflexivity|]. rewrite (amf_ssec _ _ AF). unfold step_seq. destruct (c_seq _ =? 255); rewrite Est1; reflexivity. }
           split.
           { apply (AREAS_eq_r FUEL BL _ st3); [| reflexivity]. eapply AREAS_trans; [| exact AR3]. apply AREAS_eq. rewrite step_seq_areas, Est1. reflexivity. }
           exists LS3.
           pose proof (INVL_drop_orph (xorph x0 (Some rid)) st3 L3 BL LS3 rid (mkRegion RKGroup a needed) INV3 eq_refl
                         (amf_regions _ _ AF rid _ ltac:(rewrite SS4; exact Hr1) eq_refl)) as INV4.
           cbn [r_base xorph x_idle x_zomb x_pend x_fresh x_orph] in INV4. exact INV4.
        -- intros ru Hru. cbn [answer_ok] in Hru. rewrite Hru. exact I.
      * (* [comment removed for export] *)
        intros st3 L3 LS3 g INV3 NIg AF LF AR3. cbn beta iota zeta.
        change (lh_hdr full_lay) with (fun s b => hdr_havoc b s). cbn beta.
        assert (Hr3 : s_regions st3 !! rid = Some (mkRegion RKGroup a needed)) by (apply (amf_regions _ _ AF); [rewrite SS4; exact Hr1| reflexivity]).
        assert (NS3 : s_shadow st3 !! rid = None) by (rewrite (amf_shadow _ _ AF), SS1; exact NS1).
        assert (TF3 : TF0 st3) by (apply (TF0_ctrl (step_seq st1)); [exact (amf_shadow _ _ AF)| exact (amf_tick _ _ AF)| exact TF1]).
        cbn [xidle xorph x_idle x_zomb x_pend x_orph x_fresh x0] in INV3.
        destruct (create63_ok st3 L3 BL LS3 g rid (mkRegion RKGroup a needed) needed INV3 Hr3 eq_refl eq_refl NS3 ltac:(lia) TF3)
          as (INV6 & TF6 & MR6 & GR6 & CTX6 & TK6 & RG6 & STR6 & RU6 & AR6).
        match goal with |- ftree _ (ret (upd_ctx ?f ?s6, _)) _ => set (st6 := s6) in * end.
        cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [cbn; exact (lf_live _ _ LF)|].
        split.
        { split.
          - intros q rq Hq Kq. rewrite s_regions_upd_ctx, RG6. apply (amf_regions _ _ AF); [| exact Kq]. rewrite SS4, Est1. apply (ng_keep _ _ _ _ _ _ _ INV). exact Hq.
          - rewrite s_secret_upd_ctx. transitivity (s_secret st3); [reflexivity|]. rewrite (amf_ssec _ _ AF). unfold step_seq. destruct (c_seq _ =? 255); rewrite Est1; reflexivity. }
        split.
        { apply (AREAS_eq_r FUEL BL _ st3); [eapply AREAS_trans; [| exact AR3]; apply AREAS_eq; rewrite step_seq_areas, Est1; reflexivity|].
          change (s_areas (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6) = s_areas st3). cbn. exact AR6. }
        pose proof (INVL_mmap_counter _ _ _ _ _ INV6) as INV7.
        set (st7 := upd_ctx _ st6) in *.
        assert (MR7 : MR st7 g = MR st6 g) by reflexivity.
        exists LS3, (rid, 0). rewrite MR7, MR6. cbn [m_last_idx].
        assert (SS0 : sstart (mkMeta None None (Some (rid, 0)) 0 0 0 1 63 ((needed + 4095) / 4096)) 0 = 16).
        { unfold sstart, gbase. cbn -[Z.mul Z.add get_stride]. unfold UNIT. lia. }
        rewrite SS0. change (fst (rid, 0)) with rid.
        split; [exists 0; exact GR6|]. split; [lia|]. split; [exact INV7|].
        rewrite STR6. pose proof (round_up_pg_spec needed) as [RU _].
        split; [unfold needed, IB, UNIT in *; lia|]. split; [apply TF0_TF2; apply (TF0_ctrl st6); [reflexivity| reflexivity| exact TF6]|].
        split; [unfold needed, IB, UNIT in *; lia|].
        intros _. exists (mkRegion RKGroup a needed). split; [| split; reflexivity]. change (s_regions st7) with (s_regions st6). rewrite RG6. exact Hr3.
  - intros a Ha. cbn [answer_ok] in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn iota in Ha.
    rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. exact I.
Qed.

Theorem malloc_core_ft : ltac2:(zQ "90!hla!hm4!hm0!km0!kqb!hh0!ks9!ku9!hhf@4$3@2$0$8@1$1@2$0$5$2?1L@3$7$6?2st?1n@4$4?2st?1n?1L?2BL").
Proof.
  unfold malloc_core.
  destruct (size_overflows n) eqn:Hov.
  - cbn [ftree ret]. unfold CORE_POST. cbn [fst snd]. split; [reflexivity|]. split; [apply GP_refl|]. split; [apply AREAS_refl|]. exists LS. exact INV.
  - destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hbig|Hsmall].
    + exact (malloc_big_ft Hbig Hov).
    + exact (malloc_small_ft Hsmall).
Qed.
End CORE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem malloc_INVL : ltac2:(zQ "i20!hh0!hm0!hhf!h8!ho0!kv7!hla!hh7!hp0!hq0!lc!hu0!hsa!hm4!ij4!hp5!ht6!rc!s3!jo8!kve!ija!lg4!li2!li9!km0!it7!jma!jn0!jo1!lj1!lj8!ll4!lla>2st$2>1L$h1>2BL@1$3$h2>2LS>0$7@1$3$0>1n$1>0@5$a$b^5^4^3^2>0@2$cZ^2@4$h9@2$6$2$5^6@2$hf^7^3\2L'$h1\1r@2$6$2$5@2$4@3$f@1$3$h3@1$h0^2@1$h0^8@2$4@2$hb^9@3$8$2$5^1@2$4@4$ha$hc^7^9@3$8$2$5^1Md\1x@1$d$0P@3$h5$2$5^1\1p$0@2$9$0\1c$0@2$9$1\3off$1@2$9>0$7@1$3$0\3LS'>0$7@1$3$0@2$4@3$f$0^4@2$he^3@2$i1$hd^2@2$4@2$4@2$cZ^2@2$c^2+vf@2$4@5$a$b@3$8$2$5^5^6@3$h4@2$6@2$6$0$1$1@4$e@2$6$0$1$1@4$e$0$1^3^2^9^b^1@1$h6@3$i0$0^3@4$h7$h2$h3$h8^b@2$9>0$7@1$3$0\3LS'>0$7@1$3$0@5$a$b@3$8$2$5^2^3^8^1").
Proof. intros st L BL LS n.
  intros INV Hn. unfold malloc.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  eapply ftree_bind; [exact (malloc_core_ft st0 L BL LS n INV0 TF0' Hn)|].
  intros L1 [st1 r] (LIVE & GP1 & AR1 & RES). cbn [fst snd] in RES, GP1, AR1 |- *.
  assert (GP0 : GP st st1) by (eapply GP_trans; [apply GP_eq; reflexivity| exact GP1]).
  assert (AR0 : AREAS FUEL BL st st1) by (eapply AREAS_trans; [apply AREAS_eq; reflexivity| exact AR1]).
  destruct r as [[g idx]|].
  - destruct RES as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32 & BIG).
    apply (enframe_ft (xpend x0 (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl Hn FIT TF1 RES32 BIG).
    intros off st' Ho Hf INV' CE TK. cbn [fst snd]. split; [exact LIVE|]. split; [eapply GP_trans; [exact GP0| apply GP_eq; [exact (ce_regions _ _ CE)| exact (ce_secret _ _ CE)]]|].
    split; [apply (AREAS_eq_r _ _ _ _ _ AR0); exact (ce_areas _ _ CE)|].
    exists (fst bg, sstart (MR st1 g) idx), off, LS1. split; [reflexivity|]. split; [exact Ho|]. split; [exact INV'|].
    pose proof (is_nodup _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV'))))))) as ND. cbn [map bslot fst] in ND.
    apply NoDup_cons in ND as [NI _]. intros Hin. apply NI. apply list_elem_of_In. exact Hin.
  - destruct RES as (LS1 & INV1). cbn [ftree ret fst snd]. split; [exact LIVE|]. split; [exact GP0|]. split; [exact AR0|]. exists LS1. exact INV1.
Qed.
