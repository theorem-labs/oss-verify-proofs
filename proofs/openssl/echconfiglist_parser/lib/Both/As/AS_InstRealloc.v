(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Exec CellsX Arr TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsanAllocCons AsanAllocCons2.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsDriverLaws AsSR AsChain AsUnwind FakeStackRep
     AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepX SecLazy SecGap AsDepotInv AsDepotHash
     AG_WFHit AG_MallocModel AG_Frame AG_WriteSet AW_MallocBase AG_Malloc2 AG_MallocCold AG_MallocLarge3 AG_MallocAll AG_FreeNull
     AG_Free2 AG_FreeTail AG_FreeTop AG_FreeTailR AG_FreeTopR AG_ReallocMid AG_Realloc AS_InstDefs AS_InstChain AS_InstLaws2 AS_InstHeap AS_InstFree AsWalk CidBits AG_RecycleDefs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).

Section Realloc.
  Context {HCEIL : HeapCeil}.
  Variable p : iparams.
  Hypothesis TRLEN : (length (ip_TR p) <= 4000)%nat.

  Ltac tcells := cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul length].

  (* [comment removed for export] *)
  Lemma realloc_stub_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
                                  (F : bvmap 5 word) (fc : bv 32) (m : mem),
    mem_inv asegs m ->
    evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AREALLOC_ICPT) fc None m (seg_rom asegs))
              (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AREALLOC_STUB) fc None m (seg_rom asegs)).
  Proof. intros until m. intros MI. unfold AREALLOC_STUB, AREALLOC_ICPT. step. apply evt_done. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma PINV_sii : forall st, PINV st -> PINV (set_internal_init st).
  Proof.
    intros st [CO NM]. split; [exact (COMPLETE_view st _ noX (eq_sym (cview_set_internal_init st)) CO)|].
    intros c Hc. rewrite (ncarved_view (set_internal_init st) st c (cview_set_internal_init st)). exact (NM c Hc).
  Qed.
  Lemma INITQ_sii : forall st, INITQ st -> INITQ (set_internal_init st).
  Proof. intros st IQ. exact IQ. Qed.
  Lemma sbs_sym : forall a b, same_but_shadow a b -> same_but_shadow b a.
  Proof. intros a b S. unfold same_but_shadow in *. intuition congruence. Qed.

  Theorem inst_realloc_stmt : realloc_stmt (KHp p).
  Proof.
    unfold realloc_stmt, realloc_stmt_at. cbn [as_VIS as_RHEAP as_AKREL as_alloc_ok as_Cm as_Cf as_AL as_rauxv_ok as_SR as_MPRES as_chain as_TR as_St as_lb_remove KHp].
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m x LB q A old n lo B errv mo CH bs sbs.
    intros VIS HP K INB AOK CM BLK SHD SHL AUX SPB ST CEIL LO ERR MI TP SP16 AC HCH TR A0 A1 SZ OSZ.
    destruct x as [s d]. cbn [i_s i_d] in *.
    unfold AsSR.VIS in VIS. unfold AsSR.AKREL in K. cbn [i_s cfg_model] in VIS, K. destruct K as [OK IKx]. destruct IKx as (AMX & DCOV & DTV).
    unfold Ialloc_ok, ILIVE_MAX, ILIVE_CNT_MAX, ADRV_CNT in AOK. destruct AOK as [AOK1 AOK2]. unfold Irauxv_ok in AUX. unfold AREALLOC_STACK in LO.
    pose proof HP as HP0. unfold IRHEAP in HP. cbn [i_s i_d] in HP.
    destruct HP as (HR & IDS & LEN & AWV & FLX & DEP & DPL & DTR & DF1 & DF2 & EF & MF0 & DFD & TH & TLS & ASV & DAP & DSEC & [PI IQ]).
    pose proof (proj1 HR) as R. pose proof (proj1 R) as OKs. pose proof (proj2 OKs) as W. pose proof (proj1 OKs) as PL.
    pose proof (nalloc_le_blocks s (lbp LB) m HR) as NAL. unfold lbp in NAL. rewrite zlen_map in NAL. unfold zlen in NAL.
    unfold ILIVE_CNT_MAX, ADRV_CNT in LEN.
    (* [comment removed for export] *)
    assert (INA : In (A, old) (lbp LB)) by (unfold lbp; apply in_map_iff; exists (q, A, old); split; [reflexivity| exact INB]).
    destruct (alb_In s A old (proj1 (proj2 (proj2 HR) (A, old)) INA)) as (ch & CHIN & ALLOC & EU & EN).
    pose proof (proj1 (Forall_forall _ _) IDS (q, A, old) INB) as [EQA SZB]. cbn [blk_id blk_addr blk_size fst snd] in EQA, SZB.
    (* [comment removed for export] *)
    unfold AsSR.SR.
    eapply (evt_sreach_lazy_at asegs (a_L s) (a_S s) (a_Zr s) _ msF _ mo _ OK VIS); [apply realloc_stub_evt; exact MI|].
    cbv beta. intros msF1 mo1 OK1 SBM1 _ E1.
    pose proof (AMODELX_mat s mo mo1 AMX SBM1) as AMX1. pose proof (depot_cov_mat d mo mo1 DCOV SBM1) as DCOV1.
    (* [comment removed for export] *)
    destruct (fch_of_achain m (bv_unsigned sp) (bv_unsigned s0) (a_top s) (a_bot s) (bv_unsigned ra) lo CH HCH CEIL ltac:(lia) SP16 (bv_unsigned_in_range _ ra))
      as (CHg & FCH & UTR).
    assert (PROOM : pusage (a_st s) + COLD_COST <= B_PRIM) by (pose proof (PROOM_of_PINV (a_st s) W PI); unfold COLD_COST; lia).
    assert (PR : mprimary n = true) by (apply (proj2 (mprimary_iff n ltac:(lia))); lia).
    assert (ROOM : rg_mapped_user (get_region (a_st s) (class_id (round_up (Z.max n 8) 8 + rz_size n))) + 2 * kUserMapSize <= kFreeArrayOffset).
    { destruct (mneeded_primary n ltac:(lia) PR) as (MN & RP & HC). change (round_up (Z.max n 8) 8 + rz_size n) with (mneeded n). apply (ROOM_of_PINV (a_st s) _ W PI HC). rewrite MN. exact (mused_class_pos n ltac:(lia) RP). }
    assert (NEED : 1 <= n /\ round_up (Z.max n 8) 8 + rz_size n <= kMaxSize).
    { split; [lia|]. pose proof PR as PR'. unfold mprimary, mneeded in PR'. apply Z.leb_le in PR'. exact PR'. }
    (* [comment removed for export] *)
    set (T := utrace 1833200 (bv_unsigned sp) (a_top s) (a_bot s) 30 (icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CHg)) in *.
    set (d' := d_put d (depot_hash T) (Z.of_nat (length T))) in *.
    pose proof (UTR (ip_TR p) 1833200 30 ltac:(lia) TR) as TIN. fold T in TIN.
    pose proof (utrace_length 1833200 (bv_unsigned sp) (a_top s) (a_bot s) 30 (icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) (a_top s) CHg) ltac:(lia)) as TL. fold T in TL.
    assert (DTR' : depot_tr p d').
    { apply (depot_tr_put p TRLEN d (depot_hash T) (Z.of_nat (length T)) (proj1 DEP) DTR); [apply in_map_iff; exists T; split; [reflexivity| exact TIN]| lia]. }
    destruct (d_put_blocks d (depot_hash T) (Z.of_nat (length T))) as [DNB DSB]. fold d' in DNB, DSB.
    subst A old.
    eapply (realloc_arep ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m msF1 mo1 _ s (lbp LB) d lo n CHg ch bs sbs
              HR (conj AWV FLX) AMX1 DEP DPL (conj DF1 DF2) DCOV1 MI ST CEIL ltac:(clear - LO; lia) SP16 ltac:(clear - AUX SPB; lia) NEED TP
              (dcap_of_tr p TRLEN d DTR) (dcap_of_tr p TRLEN d' DTR') FCH A0 A1 CHIN ALLOC ltac:(clear - OSZ; lia) ltac:(clear - SZ; lia) BLK (conj SHD SHL) AC PROOM ROOM).
    { (* [comment removed for export] *)
      intros sM UM stM mM HRM MODM EstM.
      pose proof (proj1 HRM) as RM. pose proof (proj1 RM) as OKM. pose proof (proj2 OKM) as WM0. rewrite EstM in WM0.
      assert (WsM : WF stM) by (eapply WF_ext; [ .. | exact WM0]; reflexivity).
      destruct (MODM 0) as (st'' & ev & MK & SBS).
      assert (W'' : WF st'') by exact (WF_sbs st'' stM SBS WsM).
      destruct (am_malloc_k_ptr_array (a_st s) n 0 UM st'' ev W MK) as [EPA0 ESB0].
      (* [comment removed for export] *)
      assert (FIND : exists chn, PositiveMap.find (ckey UM) (as_chunks st'') = Some chn /\ ch_user_beg chn = UM /\ ch_used chn = rq_size (compute_req n)).
      { destruct (am_malloc_k_frame (a_st s) n 0 UM st'' ev W MK) as (st1 & allocated & cls & CORE & EUM & _).
        destruct CORE as (_ & _ & _ & _ & _ & _ & _ & CHE & _). cbn [as_chunks upd_chunk set_chunks] in CHE.
        exists (mk_new allocated (compute_req n) cls). rewrite CHE.
        replace (ch_user_beg (mk_new allocated (compute_req n) cls)) with UM by (cbn [ch_user_beg mk_new]; lia).
        split; [apply PositiveMap.gss|]. cbn [ch_user_beg ch_used mk_new]. split; [lia| reflexivity]. }
      assert (NOLIVE : forall y, In y (chunk_list (a_st s)) -> ch_state y = CAllocated -> ch_user_beg y <> UM).
      { intros y Hy STy E.
        assert (FN : exists chn, PositiveMap.find (ckey UM) (as_chunks (a_st sM)) = Some chn /\ ch_user_beg chn = UM /\ ch_used chn = rq_size (compute_req n)).
        { rewrite EstM. change (as_chunks (set_internal_init stM)) with (as_chunks stM).
          destruct SBS as (_ & _ & _ & _ & _ & _ & _ & CH8 & _). rewrite <- CH8. exact FIND. }
        destruct FN as (chn & Fc & UB & USED).
        assert (OLD : In (UM, ch_used y) (lbp LB)).
        { apply (proj2 (proj2 (proj2 HR) _)). unfold alb. apply in_map_iff. exists y. rewrite E. split; [reflexivity|]. apply filter_In. split; [exact Hy|]. unfold is_alloc. rewrite STy. reflexivity. }
        assert (NEW : In (UM, ch_used y) (alb sM)) by (apply (proj1 (proj2 (proj2 HRM) _)); right; exact OLD).
        unfold alb in NEW. apply in_map_iff in NEW. destruct NEW as (z & Ez & Hz). apply filter_In in Hz as [Hz _].
        pose proof (WF_keys _ (proj2 (proj1 RM))) as K'. pose proof (proj1 (chunk_list_find (a_st sM) z K') Hz) as Fz.
        pose proof (f_equal fst Ez) as EUz. pose proof (f_equal snd Ez) as EUSED. cbn [fst snd] in EUz, EUSED.
        rewrite EUz in Fz. rewrite Fc in Fz. injection Fz as Ezc. subst z. rewrite USED in EUSED.
        pose proof (compute_req_facts n ltac:(lia)) as (SZr & _). cbv zeta in SZr. rewrite SZr in EUSED.
        replace (Z.max n 1) with n in EUSED by lia.
        pose proof (proj1 (proj2 HRM)) as ND'. apply NoDup_cons_iff in ND' as [NI _]. apply NI. first [rewrite <- EUSED | rewrite EUSED]. exact OLD. }
      assert (PIst : PINV st'') by (apply (PINV_am_malloc_k (a_st s) n 0 UM st'' ev W W'' PI ltac:(unfold LIVEB; clear - NAL AOK2 LEN; lia) NOLIVE MK)).
      assert (PIM : PINV stM) by exact (PINV_sbs stM st'' (sbs_sym _ _ SBS) PIst).
      assert (IQM : INITQ stM) by (apply (INITQ_core stM st'' (same_core_sbs _ _ (sbs_sym _ _ SBS))); exact (am_malloc_k_initq (a_st s) n 0 UM st'' ev W IQ MK)).
      rewrite EstM. split; [exact (INITQ_sii stM IQM)|]. split; [exact (PINV_sii stM PIM)|].
      split. { rewrite <- EstM. pose proof (nalloc_le_blocks sM ((UM, n) :: lbp LB) mM HRM) as NALM. rewrite zlen_cons in NALM. unfold lbp in NALM. rewrite zlen_map in NALM. unfold zlen in NALM. unfold LIVEB. clear - NALM AOK2 LEN. lia. }
      split; [pose proof (PROOM_of_PINV (set_internal_init stM) WM0 (PINV_sii stM PIM)); unfold COLD_COST; lia|].
      apply (ROOM_of_PINV (set_internal_init stM) kBatchClass WM0 (PINV_sii stM PIM)); [unfold kBatchClass, kNumClasses; lia| vm_compute; discriminate]. }
    { exact OK1. }
    { unfold AREALLOC_ICPT in E1. exact E1. }
    intros msF' mo' PO.
    destruct PO as (s' & U & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk & m'
                    & E_thr & E_ctx & E_fsb & E_zr & E_top & E_bot & SUB & AL
                    & OK' & VIS' & HR' & AWV' & FX' & AMX' & NV' & DEP' & DPL' & DCOV' & MI' & ST' & FR' & AVI' & CP' & AVX' & NBLK & LJ & ADDR & NEQ & MODEL).
    change (DEPOT asegs d' m') in DEP'. change (depot_placed s' d') in DPL'. change (depot_cov d' mo') in DCOV'.
    destruct MODEL as (stM & st2 & ev2 & MODM & (WFM & IQM & PIM & NALM) & MF & SBS2).
    destruct (MODM 0) as (st1 & ev1 & MK & SBS1).
    set (U0 := ch_user_beg ch) in *.
    pose proof (proj1 HR') as R'. pose proof (proj1 R') as OKs'. pose proof (proj2 OKs') as W'. pose proof (proj1 OKs') as PL'.
    (* [comment removed for export] *)
    destruct (am_malloc_k_ptr_array (a_st s) n 0 U st1 ev1 W MK) as [EPA1 ESB1].
    destruct (am_free_full_sbpa (set_internal_init stM) U0 st2 ev2 WFM MF) as [ESB2 EPA2].
    pose proof SBS1 as (Xsb1 & Xpa1 & _). pose proof SBS2 as (Xsb2 & Xpa2 & _).
    assert (ESB : a_sb s' = a_sb s).
    { unfold a_sb. rewrite <- Xsb2, ESB2. change (as_space_beg (set_internal_init stM)) with (as_space_beg stM). rewrite <- Xsb1. exact ESB1. }
    assert (EPA : a_pa s' = a_pa s).
    { unfold a_pa. rewrite <- Xpa2, EPA2. change (as_ptr_array (set_internal_init stM)) with (as_ptr_array stM). rewrite <- Xpa1. exact EPA1. }
    (* [comment removed for export] *)
    assert (PI' : PINVI (a_st s')).
    { assert (SC : same_core (a_st s') st2) by (apply same_core_sbs; exact (sbs_sym _ _ SBS2)).
      split.
      - apply (PINV_core (a_st s') st2 SC). exact (PINV_am_free_full (set_internal_init stM) U0 st2 ev2 WFM PIM NALM MF).
      - apply (INITQ_core (a_st s') st2 SC). exact (proj1 (am_free_full_initq (set_internal_init stM) U0 st2 ev2 WFM IQM MF)). }
    (* [comment removed for export] *)
    pose proof TH as (TH1 & TH2 & DPOS & DM8 & DCE & AKD).
    pose proof CP' as AG'. unfold acompl in AG'.
    assert (AGR : agree_on (fun a => ~ awrit s s' d lo (bv_unsigned sp) a) m m') by (intros x0 Hx Hr; exact (AG' x0 Hr Hx)).
    pose proof (vis_off_awrit s s' PL d lo (bv_unsigned sp) m m' AVI') as VOFF.
    assert (DTV1 : dtv_cov p mo1) by (intros x0 Hx; rewrite (same_but_materialized_vmmaps mo mo1 SBM1); exact (DTV x0 Hx)).
    assert (IMGW : forall a, AIMG_LO <= a < AIMG_TOP -> ~ astatw a -> ~ awrit s s' d lo (bv_unsigned sp) a).
    { intros a H1 H2. exact (image_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL H1 H2). }
    assert (DTVW : forall a, ip_D p <= a < ip_D p + 32 -> ~ awrit s s' d lo (bv_unsigned sp) a).
    { intros a Ha. exact (dtv_not_written p s s' d lo (bv_unsigned sp) mo1 mo' a PL PL' E_thr ESB EPA CEIL AKD DCE DPOS DAP DSEC DTV1 AVX' Ha). }
    assert (ELB : lbp (Ilb_remove q LB) = lb_remove U0 (lbp LB)) by (rewrite (lbp_remove q LB IDS), EQA; reflexivity).
    assert (URNG : arblock_range U n) by exact (ARHEAP_block_range_thm s' OKs' ((U, n) :: lb_remove U0 (lbp LB)) m' U n HR' (or_introl eq_refl)).
    assert (RH' : IRHEAP p (IST s' d') ((U, U, n) :: Ilb_remove q LB) m').
    { unfold IRHEAP. cbn [i_s i_d]. change (lbp ((U, U, n) :: Ilb_remove q LB)) with ((U, n) :: lbp (Ilb_remove q LB)). rewrite ELB.
      split; [exact HR'|].
      split. { constructor; [cbn [blk_id blk_addr blk_size fst snd]; split; [reflexivity| clear - SZ; lia]|].
               apply Forall_forall; intros b Hb; exact (proj1 (Forall_forall _ _) IDS b (proj1 (Ilb_remove_incl q LB b Hb))). }
      split; [pose proof (Ilb_remove_length q LB) as LL; cbn [length]; rewrite Nat2Z.inj_succ; unfold ILIVE_CNT_MAX, ADRV_CNT; clear - LL LEN AOK2; lia|].
      split; [exact AWV'|]. split; [exact FX'|]. split; [exact DEP'|]. split; [exact DPL'|]. split; [exact DTR'|].
      split; [rewrite E_fsb, DNB; exact DF1|]. split; [rewrite E_fsb, DSB; exact DF2|].
      split; [rewrite E_fsb; exact EF|]. split; [exact MF0|]. split; [rewrite E_fsb; exact DFD|].
      split.
      { unfold ATHR. split; [| split; [| exact (conj DPOS (conj DM8 (conj DCE AKD)))]].
        - eapply (rw_cells_transport_vis _ m m' _ _ AGR VOFF TH1). tcells.
          intros a Ha. apply IMGW; unfold astatw, ATP, AIMG_LO, AIMG_TOP, AINST, AIAINIT, AIAINST in *; lia.
        - eapply (rw_cells_transport_vis _ m m' _ _ AGR VOFF TH2). tcells.
          intros a Ha. apply DTVW. lia. }
      split.
      { destruct TLS as (tb & te & TC). exists tb, te. rewrite E_thr. eapply (rw_cells_transport_vis _ m m' _ _ AGR VOFF TC). tcells.
        intros a Ha. exact (thread_head_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL ltac:(lia)). }
      split; [exact (proj1 (proj2 (proj1 AMX')))|].
      split; [unfold IDAPART; rewrite ESB, E_thr, EPA, DNB, DSB; exact DAP|].
      split; [| exact PI'].
      intros sc Hsc. exact (DSEC sc (SUB sc Hsc)). }
    apply sreach_done. unfold realloc_post.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', errv, U, (skipn (Z.to_nat (Z.min n (ch_used ch))) junk), U, (IST s' d').
    cbn [as_VIS as_RHEAP as_AKREL as_alloc_ok as_Cm as_Cf as_AL as_rauxv_ok as_SR as_MPRES as_chain as_TR as_St as_FSB as_lb_remove KHp i_s i_d].
    split; [unfold AsSR.VIS; cbn [i_s]; exact VIS'|].
    split. { unfold AsSR.AKREL. cbn [i_s i_d cfg_model cfg_ms]. split; [exact OK'|]. split; [exact AMX'|]. split; [exact DCOV'|].
             intros x0 Hx. destruct (proj1 (AVX' x0 (DTV1 x0 Hx))) as [C|(sc & INs & _ & Rx)]; [exact C| exfalso].
             pose proof (DSEC sc INs) as DS. clear - DS Rx Hx. unfold disj, kPageSize in *. lia. }
    split; [exact (nonvm_same_trans _ _ _ (nonvm_same_mat mo mo1 SBM1) NV')|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { rewrite TP. unfold wz. rewrite unsigned_lit by (unfold AsIface.ATP; lia). rewrite TP in ERR. rewrite unsigned_lit in ERR by (unfold AsIface.ATP; lia).
             eapply (rw_cells_transport_vis _ m m' _ _ AGR VOFF ERR). tcells.
             intros a Ha. apply IMGW; unfold astatw, AsIface.ATP, AIMG_LO, AIMG_TOP, AINST, AIAINIT, AIAINST in *; lia. }
    split; [exact AUX|].
    split. { (* [comment removed for export] *)
             intros a Ha CL.
             assert (BLKIN : forall b, In b (Ilb_remove q LB) -> In (blk_addr b, blk_size b) (lb_remove U0 (lbp LB))).
             { intros b Hb. rewrite <- ELB. unfold lbp. apply in_map_iff. exists b. split; [reflexivity| exact Hb]. }
             assert (BLKIN' : forall b, In b (Ilb_remove q LB) -> In (blk_addr b, blk_size b) ((U, n) :: lb_remove U0 (lbp LB))) by (intros b Hb; right; exact (BLKIN b Hb)).
             split.
             - apply (FR' a Ha). unfold aclient_addr in CL. unfold aclient. cbn [as_FSB KHp] in CL.
               destruct CL as [C|[C|[C|[C|[C|[C|C]]]]]]; [left; exact C| right; left; exact C| | | | |].
               + right; right; left. destruct C as (b & Hb & Rb). exists (blk_addr b), (blk_size b). split; [exact (BLKIN b Hb)| exact Rb].
               + right; right; right; left. destruct C as (b & Hb & Rb). exists (blk_addr b), (blk_size b). split; [exact (BLKIN b Hb)| exact Rb].
               + do 4 right; left. rewrite EF. exact C.
               + do 5 right; left. rewrite EF. exact C.
               + do 6 right. exact C.
             - intros Wv. destruct (AVI' (wa a) Wv) as [V|G]; [exact V| exfalso]. rewrite wa_unsigned in G by exact Ha.
               revert G. unfold aclient_addr in CL. cbn [as_FSB KHp] in CL.
               destruct CL as [C|[C|[C|[C|[C|[C|C]]]]]].
               + apply (secgone_not_stack s s' PL a lo CEIL). clear - C LO. lia.
               + apply (secgone_not_image s s' PL a). clear - C. unfold aimg_client, AIMG_LO, AIMG_TOP in *. lia.
               + destruct C as (b & Hb & Rb). destruct (alb_In s' _ _ (proj1 (proj2 (proj2 HR') _) (BLKIN' b Hb))) as (chb & CHB & _ & EUb & ENb).
                 apply (secgone_not_block s s' PL chb a W OKs' ESB SUB CHB). left. rewrite EUb, ENb. exact Rb.
               + destruct C as (b & Hb & Rb). destruct (alb_In s' _ _ (proj1 (proj2 (proj2 HR') _) (BLKIN' b Hb))) as (chb & CHB & _ & EUb & ENb).
                 apply (secgone_not_block s s' PL chb a W OKs' ESB SUB CHB). right. rewrite EUb, ENb. exact Rb.
               + apply (secgone_not_fsb s s' PL a). left. rewrite EF. exact C.
               + apply (secgone_not_fsb s s' PL a). right. rewrite EF. exact C.
               + apply (secgone_not_stkshadow s s' PL a). exact C. }
    split; [exact (inst_RHEAP_block_range p (IST s' d') ((U, U, n) :: Ilb_remove q LB) m' (U, U, n) RH' (or_introl eq_refl))|].
    split; [exact RH'|].
    split. { (* [comment removed for export] *)
             pose proof (rw_cells_split_CB asegs m' U [] (Z.to_nat n) (firstn (Z.to_nat (Z.min n (ch_used ch))) bs ++ skipn (Z.to_nat (Z.min n (ch_used ch))) junk) []
                           [Z.to_nat (Z.min n (ch_used ch)); Z.to_nat (n - Z.min n (ch_used ch))]%nat NBLK ltac:(cbn [sum_nat Nat.add]; clear - SZ SZB; lia)) as X.
             cbn [app mk_CB_cells] in X.
             assert (LBS : length bs = Z.to_nat (ch_used ch)) by (destruct BLK as [[[L _] _] _]; exact L).
             assert (LF : length (firstn (Z.to_nat (Z.min n (ch_used ch))) bs) = Z.to_nat (Z.min n (ch_used ch))) by (rewrite length_firstn; clear - LBS SZ OSZ; lia).
             rewrite firstn_app, LF, Nat.sub_diag, firstn_O, app_nil_r, firstn_firstn in X. rewrite Nat.min_id in X.
             rewrite skipn_app, LF, Nat.sub_diag, skipn_O, skipn_firstn_comm, Nat.sub_diag, firstn_O, app_nil_l in X.
             rewrite (@firstn_all2 _ (Z.to_nat (n - Z.min n (ch_used ch))) (skipn (Z.to_nat (Z.min n (ch_used ch))) junk)) in X by (rewrite length_skipn, LJ; clear - SZ SZB; lia).
             rewrite (Z.min_comm (ch_used ch) n). exact X. }
    split; [exact ADDR|].
    split. { (* [comment removed for export] *)
             assert (NWC : forall a, aconst_addr a -> ~ awrit s s' d lo (bv_unsigned sp) a).
             { intros a HC. unfold aconst_addr in HC.
               unfold AsConst.ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL, AVERBOSITY_CELL,
                 AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL in HC.
               destruct (Z.lt_ge_cases a AIMG_TOP) as [LT|GE].
               + apply IMGW; unfold astatw, sh, ASHADOW_BASE, AIMG_LO, AIMG_TOP, AINST, AIAINIT, AIAINST in *; clear - HC LT; lia.
               + apply (imgshadow_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL). unfold sh, ASHADOW_BASE, AIMG_LO, AIMG_TOP in *; clear - HC GE; lia. }
             eapply (ACONST_ext_pt m m' AC).
             - intros a Ha HC. apply (AGR a); [exact (NWC a HC)| exact Ha].
             - intros a Ha HC Wv. apply VOFF; [rewrite wa_unsigned by exact Ha; exact (NWC a HC)| exact Wv].
             - intros a Ha. destruct AC as (_ & _ & (S0 & S1 & SS)). destruct (SS a Ha) as [W0 (b & Hb)]. exists b.
               unfold mrd in *. rewrite (AGR a); [exact Hb| | unfold sh, AIMG_LO, AIMG_TOP, ASHADOW_BASE in *; lia].
               exact (imgshadow_not_written s s' d lo (bv_unsigned sp) a PL PL' E_thr DPL CEIL Ha). }
    unfold ICm, ICf. unfold FREE_COST in AL. replace (n <=? 64512) with true by (symmetry; apply Z.leb_le; clear - SZ; lia). clear - AL. lia.
  Qed.
End Realloc.
