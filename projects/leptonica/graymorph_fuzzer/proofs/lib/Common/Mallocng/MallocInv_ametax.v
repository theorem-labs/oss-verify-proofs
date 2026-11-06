(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocInv_defs MallocInv_heap MallocInv_word
  MallocInv_sep MallocInv_wf MallocInv_wf3 MallocInv_wf4 MallocInv_dll MallocInv_tables MallocInv_steps MallocInv_repw
  MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_vmops MallocInv_auxv
  MallocInv_ameta_base MallocInv_ameta_iface MallocInv_ameta1 MallocInv_ameta2 MallocInv_ameta3
  MallocInv_budget MallocInv_ameta4 MallocInv_ameta5 MallocInv_ametax_iface MallocInv_ameta5x MallocInv_ameta6x.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition am_pop (m : word) : M word :=
  nx <- m_ld (at_ m 8) ;;
  (if c_eq nx m then m_sd A_FREE_META_HEAD w0
   else pv <- m_ld m ;;
        m_sd (at_ pv 8) nx ;;
        pv2 <- m_ld m ;;
        nx2 <- m_ld (at_ m 8) ;;
        m_sd nx2 pv2 ;;
        h <- m_ld A_FREE_META_HEAD ;;
        if c_eq h m then n3 <- m_ld (at_ m 8) ;; m_sd A_FREE_META_HEAD n3
        else mret tt) ;;
  m_sd (at_ m 8) w0 ;; m_sd m w0 ;;
  mret m.

Definition am_carve (amc : word) : M word :=
  m <- m_ld A_AVAIL_META ;;
  m_sd A_AVAIL_META (at_ m 40) ;;
  m_sd A_AVAIL_META_CNT (v_addi amc (-1)) ;;
  m_sd (at_ m 8) w0 ;; m_sd m w0 ;;
  mret m.

Definition am_body : M word :=
  fmh <- m_ld A_FREE_META_HEAD ;;
  if negb (is0 fmh) then
    let m := fmh in am_pop m
  else
  amc <- m_ld A_AVAIL_META_CNT ;;
  if negb (is0 amc) then am_carve amc
  else
  aac <- m_ld A_AVAIL_AREA_CNT ;;
  r <- am_prov aac ;;
  am_tail r.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dom_transport : forall A A' x, gsame A A' -> a_areas A' = a_areas A -> a_pages A' = a_pages A ->
  dom A' x -> dom A x.
Proof.
  intros A A' x HG Ea Ep Hd. destruct Hd as [(pg & Hpg & Hx) | [(ma & mt & aib & sl & Hma & Hr & Hml & Hx) | (pg & Hpg & Hx)]].
  - left. exists pg. rewrite <- Ea. auto.
  - right; left. exists ma, mt, aib, sl. split; [exact (gs_grp_back A A' HG ma mt aib sl Hma Hr) | auto].
  - right; right. exists pg. rewrite <- Ep. auto.
Qed.

Lemma fmh_range : forall A, WF A -> 0 <= a_ctx A KFmh < 2^64.
Proof.
  intros A HW. pose proof (wf_fl_head A HW) as Hh. pose proof (wf_ctx_nonneg A HW KFmh). split; [lia|].
  destruct (a_freelist A) as [|x l] eqn:E; [cbn in Hh; lia|]. cbn in Hh.
  destruct (proj1 (wf_fl_mem A HW x) ltac:(rewrite E; left; reflexivity)) as (mt & Hx & _).
  destruct (proj1 (wf_meta_dom A HW x) ltac:(rewrite Hx; discriminate)) as (pg & k & Hpg & Hk & Ex).
  destruct (wf_areas_al A HW pg Hpg) as [_ (R1 & R2 & R3 & R4)]. unfold meta_addr in Ex. ceil. lia.
Qed.

Section Body.
  Variable W : wmode.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A0 : astate) (s0 : mstate).

  Local Notation PreT := (PreTX W sp0 argv envp cb D A0 s0).
  Local Notation PreM := (PreM sp0 argv envp cb D A0 s0).
  Local Notation BodyPost := (BodyPostX W sp0 argv envp cb D A0 s0).
  Local Notation ProvPost := (ProvPost W sp0 argv envp cb D A0 s0).

  (* [comment removed for export] *)
  Record PreB (A : astate) (s : mstate) : Prop := {
    pb_ii : II sp0 argv envp cb D A s;
    pb_fr : FR A0 s0 A s;
    pb_gs : gsame A0 A;
    pb_areas : a_areas A = a_areas A0;
    pb_pages : a_pages A = a_pages A0;
    pb_fl : a_freelist A = a_freelist A0;
    pb_amc : a_ctx A KAmc = a_ctx A0 KAmc;
    pb_aac : a_ctx A KAac = a_ctx A0 KAac;
    pb_vm : ms_vm s = ms_vm s0;
    pb_init : a_ctx A KInit = 1;
    pb_xm : a_xmaps A = a_xmaps A0;
    pb_shift : a_ctx A KShift = a_ctx A0 KShift (* [comment removed for export] *) }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem prov_ok : forall A s, PreB A s -> a_ctx A KAmc = 0 -> a_freelist A = [] -> spare A0 = 0 ->
    tsall W (am_prov (Z_to_bv 64 (a_ctx A KAac)) s) ProvPost.
  Proof.
    intros A s PB Hamc Hfl Hsp0. destruct PB as [HII HFR HGS Hareas Hpages Hfl0 Hamc0 Haac0 Hvm Hinit Hxm Hshift].
    pose proof HII as [HI HVo HAV HUS HD]. pose proof HI as [HW HR HC HWIN HE HG].
    pose proof (VMok_core A _ HVo) as HVc. ceil.
    pose proof HVo as [Vg Vb Va Vres Vbv Vpw Vmw Vna Vac Vpc Vall Vspan Vtop].
    pose proof (wf_ctx_nonneg A HW KAac) as Haac_nn.
    assert (Hdom : forall x, dom A x -> dom A0 x) by (intros x; apply (dom_transport A0 A x HGS Hareas Hpages)).
    assert (Hdom2 : forall x, dom A x <-> dom A0 x).
    { intros x. split; [apply Hdom|]. pose proof HGS as [G1 G2 G3 G4 G5 G6].
      intros [(pg & Hpg & Hx) | [(ma & mt & aib & sl & Hma & Hr & Hml & Hx) | (pg & Hpg & Hx)]].
      - left. exists pg. rewrite Hareas. auto.
      - right; left. exists ma, mt, aib, sl. split; [exact (G1 ma mt aib sl Hma Hr) | auto].
      - right; right. exists pg. rewrite Hpages. auto. }
    unfold am_prov.
    destruct (Z.eq_dec (a_ctx A KAac) 0) as [Haac | Haac].
    - (* [comment removed for export] *)
      rewrite Haac, is0_true. cbn [negb]. rewrite A_BRK_eq.
      assert (HbrkR : 0 <= a_ctx A KBrk < 2^64).
      { destruct (vc_brk_valid A _ HVc) as (K1 & K2 & K3 & K4). destruct Vb as [E | [E | (E & _)]]; rewrite E; lia. }
      eapply (tw_ld_ctx W A); [exact HW | exact HR | exact HWIN | exact I | reflexivity | exact HbrkR |].
      assert (PM : PreM A s).
      { constructor; try assumption. rewrite <- Haac0. exact Haac. }
      destruct Vb as [E | [E | (E & _)]].
      + rewrite E. apply (brk_c_ok W sp0 argv envp cb D A0 s0 A s PM E).
      + rewrite E. apply (brk_a_ok W sp0 argv envp cb D A0 s0 A s PM E).
      + apply (brk_b_ok W sp0 argv envp cb D A0 s0 A s PM E).
    - (* [comment removed for export] *)
      destruct (Va ltac:(lia)) as (R1 & R2 & R3 & R4).
      pose proof (wf_ctx_nonneg A HW KAareas) as Hp0.
      rewrite is0_false by lia. cbn [negb]. rewrite A_AVAIL_AREAS_eq.
      eapply (tw_ld_ctx W A); [exact HW | exact HR | exact HWIN | exact I | reflexivity | lia |].
      apply tw_ret'. cbn [MallocInv_ameta6x.ProvPost]. exists 0, A, (a_ctx A KAareas). split; [reflexivity|].
      constructor; try assumption.
      + apply AMK_vm; [exact Hvm | exact Hdom | lia].
      + lia.
      + lia.
      + reflexivity.
      + intros b sz Hin Hf. rewrite <- Hvm in Hin, Hf.
        destruct (proj1 (map_contains_mcov _ _ _) R4) as (nb & nsz & Hnin & N1 & N2). rewrite !uZ in N1 by lia. rewrite !uZ in N2 by lia.
        pose proof (region_free_In _ _ _ _ _ Hf Hnin) as Ho. unfold iv_overlap in Ho.
        apply andb_false_iff in Ho. destruct Ho as [Ho | Ho]; apply Z.ltb_ge in Ho; lia.
      + intros Hb. rewrite Hvm. destruct Hb as [Hsp | [Hbud _]]; [lia | exact Hbud].
      + intros _ _. rewrite Hvm. apply am_pre_refl.
      + rewrite Hvm. apply am_preg_refl.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem body_ok : forall A s, PreB A s -> tsall W (am_body s) BodyPost.
  Proof.
    intros A s PB. pose proof PB as [HII HFR HGS Hareas Hpages Hfl0 Hamc0 Haac0 Hvm Hinit Hxm Hshift].
    pose proof HII as [HI HVo HAV HUS HD]. pose proof HI as [HW HR HC HWIN HE HG]. ceil.
    assert (Hdom : forall x, dom A x -> dom A0 x) by (intros x; apply (dom_transport A0 A x HGS Hareas Hpages)).
    assert (Hspare : spare A = spare A0) by (unfold spare; rewrite Hfl0, Hamc0; reflexivity).
    unfold am_body. rewrite A_FREE_META_HEAD_eq.
    eapply (tw_ld_ctx W A); [exact HW | exact HR | exact HWIN | exact I | reflexivity | exact (fmh_range A HW) |].
    pose proof (wf_fl_head A HW) as Hfmh.
    destruct (a_freelist A) as [|m rest] eqn:Efl.
    - (* [comment removed for export] *)
      cbn in Hfmh. rewrite Hfmh, is0_true. cbn [negb]. rewrite A_AVAIL_META_CNT_eq.
      pose proof (wf_amc A HW) as Hamc.
      eapply (tw_ld_ctx W A); [exact HW | exact HR | exact HWIN | exact I | reflexivity | lia |].
      destruct (Z.eq_dec (a_ctx A KAmc) 0) as [Hamc0' | HamcP].
      + (* [comment removed for export] *)
        rewrite Hamc0', is0_true. cbn [negb]. rewrite A_AVAIL_AREA_CNT_eq.
        pose proof (wf_ctx_nonneg A HW KAac).
        assert (HaacR : a_ctx A KAac < 2^64).
        { pose proof (wf_ctx_nonneg A HW KAareas). destruct (Z.eq_dec (a_ctx A KAac) 0) as [E | Hne]; [lia|]. destruct (vm_areas_res A _ HVo ltac:(lia)) as (_ & R2 & _). lia. }
        eapply (tw_ld_ctx W A); [exact HW | exact HR | exact HWIN | exact I | reflexivity | lia |].
        assert (Hsp0 : spare A0 = 0) by (rewrite <- Hspare; unfold spare; rewrite Efl, Hamc0'; reflexivity).
        apply (tw_bind_post W (am_prov (Z_to_bv 64 (a_ctx A KAac))) am_tail s ProvPost).
        * apply (prov_ok A s PB Hamc0' Efl Hsp0).
        * intros r s' HP. apply (tail_ok W sp0 argv envp cb D A0 s0 r s' HP).
      + (* [comment removed for export] *)
        rewrite is0_false by lia. cbn [negb]. unfold am_carve.
        apply tsall_of_tsafe. apply (tsafe_leaves_of_cps _ s BodyPost). intros K' P' HK'.
        apply (carve_ok sp0 argv envp cb A s HI HVo ltac:(lia) D HD HAV K' P').
        intros s' A' HI' HVo' Hvm' HFR' HGM Hareas' Hamc' Hfl' Hpages' Hmb' Hxm' Hctx'.
        apply HK'. right. eexists. split; [reflexivity|]. exists A'.
        pose proof HGM as [G1 G2 G3 G4 G5 G6 G7 G8].
        split; [rewrite Hvm', Hvm; apply am_grow_refl|].
        split; [| split; [| split; [| split; [| split; [rewrite Hxm'; exact Hxm | split; [intros _ _; rewrite Hvm', Hvm; apply am_delta_refl |]]]]]].
        * constructor; [exact HI' | exact HVo' | exact G8 | apply (UsOK_transport A A' G7 Hareas' HUS) | exact G5].
        * apply (FR_trans A0 s0 A s); assumption.
        * apply (got_meta_pre A0 A); assumption.
        * apply (AMvm_of_AMK 0); [| lia]. apply AMK_vm; [rewrite Hvm'; exact Hvm | | lia].
          intros x Hx. apply Hdom. apply (dom_transport A A' x G7 Hareas' Hpages' Hx).
        * left. split; [rewrite <- Hspare; unfold spare; rewrite Efl; cbn; lia|].
          split; [rewrite Hvm'; exact Hvm|]. split; [rewrite Hareas'; exact Hareas|].
          rewrite <- Hspare. unfold spare. rewrite Hfl', Efl, Hamc'. cbn. lia.
    - (* [comment removed for export] *)
      cbn in Hfmh. rewrite Hfmh.
      destruct (proj1 (wf_fl_mem A HW m) ltac:(rewrite Efl; left; reflexivity)) as (mt & Hm & _).
      destruct (proj1 (wf_meta_dom A HW m) ltac:(rewrite Hm; discriminate)) as (pg & k & Hpg & Hk & Em).
      destruct (wf_areas_al A HW pg Hpg) as [_ (R1 & R2 & R3 & R4)]. unfold meta_addr in Em.
      rewrite is0_false by lia. cbn [negb]. cbv zeta. unfold am_pop.
      apply tsall_of_tsafe. apply (tsafe_leaves_of_cps _ s BodyPost). intros K' P' HK'.
      apply (pop_ok sp0 argv envp cb A s HI HVo m rest Efl D HD HAV K' P').
      intros s' A' HI' HVo' Hvm' HFR' HGM Hareas' Hamc' Hfl' Hctx' Hpages' Hmb' Hxm'.
      apply HK'. right. exists m. split; [reflexivity|]. exists A'.
      pose proof HGM as [G1 G2 G3 G4 G5 G6 G7 G8].
      split; [rewrite Hvm', Hvm; apply am_grow_refl|].
      split; [| split; [| split; [| split; [| split; [rewrite Hxm'; exact Hxm | split; [intros _ _; rewrite Hvm', Hvm; apply am_delta_refl |]]]]]].
      + constructor; [exact HI' | exact HVo' | exact G8 | apply (UsOK_transport A A' G7 Hareas' HUS) | exact G5].
      + apply (FR_trans A0 s0 A s); assumption.
      + apply (got_meta_pre A0 A); assumption.
      + apply (AMvm_of_AMK 0); [| lia]. apply AMK_vm; [rewrite Hvm'; exact Hvm | | lia].
        intros x Hx. apply Hdom. apply (dom_transport A A' x G7 Hareas' Hpages' Hx).
      + pose proof (wf_amc A HW). left. split; [rewrite <- Hspare; unfold spare; rewrite Efl; cbn [length]; rewrite Nat2Z.inj_succ; lia|].
        split; [rewrite Hvm'; exact Hvm|]. split; [rewrite Hareas'; exact Hareas|].
        rewrite <- Hspare. unfold spare. rewrite Hfl', Efl, Hamc'. cbn [length]. rewrite Nat2Z.inj_succ. lia.
  Qed.
End Body.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma PreB_refl : forall sp0 argv envp cb D A s,
  II sp0 argv envp cb D A s -> a_ctx A KInit = 1 -> PreB sp0 argv envp cb D A s A s.
Proof.
  intros sp0 argv envp cb D A s HII H1. constructor; try reflexivity; [exact HII | apply FR_refl | apply gsame_refl | exact H1].
Qed.

Lemma PreB_init : forall sp0 argv envp cb D A s s1 sec,
  II sp0 argv envp cb D A s ->
  IS sp0 argv envp cb (initA A sec) s1 -> FR A s (initA A sec) s1 -> ms_vm s1 = ms_vm s -> a_ctx (initA A sec) KInit = 1 ->
  PreB sp0 argv envp cb D A s (initA A sec) s1.
Proof.
  intros sp0 argv envp cb D A s s1 sec HII HI1 HFR1 Hvm1 Hinit1. pose proof HII as [HI HVo HAV HUS HD].
  assert (HG : gsame A (initA A sec)).
  { constructor; try reflexivity; try (intros; assumption). intros kk Hk Hv. unfold initA, set_ctx. cbn [a_ctx].
    apply init_ctx_other; destruct kk; cbn in Hk; try contradiction; discriminate. }
  constructor; try reflexivity; try assumption.
  constructor; [exact HI1 | | | | intros x; exact (HD x)].
  + rewrite Hvm1. unfold initA. apply VMok_set_ctx; [exact HVo | | |]; rewrite ?init_ctx_other by discriminate.
    * exact (vm_brk_ok A _ HVo).
    * exact (vm_areas_res A _ HVo).
    * exact (proj1 (vm_brk_span A _ HVo)).
  + intros ma mt Hma Hr. unfold initA, set_ctx. cbn [a_ctx a_areas]. rewrite init_ctx_other by discriminate. exact (HAV ma mt Hma Hr).
  + apply (UsOK_transport A _ HG); [reflexivity | exact HUS].
Qed.

Theorem alloc_meta_okX : alloc_meta_specX.
Proof.
  intros W R sp0 argv envp cb D A s sp K P HII Hfail Hsucc.
  pose proof HII as [HI HVo HAV HUS HD]. pose proof HI as [HW HR HC HWIN HE HG].
  unfold m_alloc_meta. treassoc.
  (* [comment removed for export] *)
  eapply (tw_det W m_canary_load s _ P (A_SSP, le_val cb) s).
  { intros K' P' HK'. apply ts_canary_load; [exact (envok_statics _ _ _ _ HE) | exact HWIN |].
    intros cb' Hcb'. unfold GRD in HG. rewrite HG in Hcb'. injection Hcb' as <-. exact HK'. }
  cbv beta iota.
  (* [comment removed for export] *)
  treassoc. rewrite A_INIT_DONE_eq at 1.
  pose proof (wf_init A HW) as Hini.
  eapply (tw_det W (m_lw (Z_to_bv 64 (caddr KInit))) s _ P (Z_to_bv 64 (bv_swrap 32 (a_ctx A KInit))) s).
  { intros K' P' HK'. eapply (ts_lw_ctx A); [exact HR | exact HWIN | exact I | reflexivity | destruct Hini as [E|E]; rewrite E; lia | exact HK']. }
  cbv beta. treassoc.
  (* [comment removed for export] *)
  match goal with |- tsall _ (mbind _ ?TK s) _ =>
    assert (COMMON : forall A1 s1, PreB sp0 argv envp cb D A s A1 s1 -> tsall W (TK tt s1) P) end.
  { intros A1 s1 PB1. pose proof PB1 as [HII1 HFR1 HGS1 Hareas1 Hpages1 Hfl1 Hamc1 Haac1 Hvm1 Hinit1 Hxm1 Hshift1].
    pose proof HII1 as [HI1 _ _ _ _].
    cbv beta. treassoc. rewrite at_libc48.
    eapply (tw_ld_pagesize W sp0 argv envp cb A1); [exact HI1|].
    treassoc. apply tw_assert; [apply c_eq_refl|].
    change (c_ltu (wlit 4096) (Z_to_bv 64 4096)) with false. cbv iota. cbv zeta.
    treassoc.
    apply (tw_bind_post W am_body _ s1 (BodyPostX W sp0 argv envp cb D A s)).
    - apply (body_ok W sp0 argv envp cb D A s A1 s1 PB1).
    - intros res s' HP.
      destruct HP as [[-> HF] | (m & -> & HS)].
      + destruct HF as (A' & [Hgrow' Hroom'] & HII' & HFR' & HGS' & HAM' & Hsp & Har & HWOk & Hxm' & Hdom'). pose proof HII' as [[_ _ _ HWIN' _ HG'] _ _ _ _].
        treassoc. eapply (tw_det W (m_canary_check A_SSP (le_val cb)) s' _ P tt s').
        { intros K' P' HK'. apply (ts_canary_check s' cb); [exact HWIN' | exact HG' | exact HK']. }
        apply tw_bind_ret. rewrite <- w0_eq. apply (Hfail s' A'); assumption.
      + destruct HS as (A' & Hgrow' & HII' & HFR' & HGM' & HAM' & Hxm' & Hdelta & Hdisj). pose proof HII' as [[_ _ _ HWIN' _ HG'] _ _ _ _].
        treassoc. eapply (tw_det W (m_canary_check A_SSP (le_val cb)) s' _ P tt s').
        { intros K' P' HK'. apply (ts_canary_check s' cb); [exact HWIN' | exact HG' | exact HK']. }
        apply tw_bind_ret. apply (Hsucc s' A' m); assumption. }
  destruct Hini as [E0 | E1].
  - (* [comment removed for export] *)
    rewrite E0. change (negb (is0 (Z_to_bv 64 (bv_swrap 32 0)))) with false. cbv iota.
    eapply (tw_lift W _ s (fun _ s1 => exists A1, IS sp0 argv envp cb A1 s1 /\ FR A s A1 s1 /\ ms_vm s1 = ms_vm s /\ a_ctx A1 KInit = 1 /\ exists sec, A1 = initA A sec)).
    + intros K' P' HK'. apply (init_else_ok sp0 argv envp cb A s sp HI K' P' E0).
      intros s1 A1 H1 H2 H3 H4 H5. apply HK'. exists A1. auto.
    + intros [] s1 (A1 & HI1 & HFR1 & Hvm1 & Hinit1 & [sec ->]).
      apply (COMMON (initA A sec) s1). apply (PreB_init sp0 argv envp cb D A s s1 sec HII HI1 HFR1 Hvm1 Hinit1).
  - (* [comment removed for export] *)
    rewrite E1. change (negb (is0 (Z_to_bv 64 (bv_swrap 32 1)))) with true. cbv iota.
    apply tw_bind_ret. apply (COMMON A s). apply (PreB_refl sp0 argv envp cb D A s HII E1).
Qed.

(* [comment removed for export] *)
Theorem alloc_meta_ok' : alloc_meta_spec.
Proof. exact (alloc_meta_specX_spec alloc_meta_okX). Qed.

End WithLayout.
