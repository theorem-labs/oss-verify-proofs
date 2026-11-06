(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtA CutHeapV.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ESMK.
Definition mem := (word -> option byte).
Section Inst.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LY_img : 0 <= hl_img_lo L /\ hl_img_hi L <= BIGSHADOW_LO.
Hypothesis LY_ro : forall a, hl_rt_ro L a -> hl_img_lo L <= a < hl_img_hi L.
Hypothesis LY_below : segs_below_b (hl_segs L) (hl_img_hi L) = true.
Hypothesis LY_nowrap : wx_segs_nowrap (hl_segs L).
Variable IMGHI : Z.                      (* [comment removed for export] *)
Hypothesis LY_imghi : IMGHI <= hl_img_hi L /\ hl_img_lo L < FS_BYTES.
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable A0 : list (Z * Z).
Variable LBrest : list (Z * Z).
Variable FFrest : list fframe.
Variable LK0 : list fframe.
Variable sp0 : Z.
Variable d : CH.hdecl.
Abbreviation SCR := (CH.hd_scr d).
Variable W : list L5.range.
Variable Wo : list L5.range.
Variable BLS : list CA.blocks.
Variable FFS : list (list (expr * Z * Z)).
Variable Cred : nat -> env -> credit -> Prop.
Variable D0 : Z.
Hypothesis STK : sp0 mod 16 = 0 /\ ahl_ceil ar + 4096 + SCR <= sp0 /\ sp0 <= ar_sptop ar.
Hypothesis SCR_pos : 0 <= SCR.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis Wo_incl : incl Wo W.
Hypothesis Wo_ok : forall r a, In r Wo -> L5.in_rng r a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LBrest FFrest sp0 SCR a
  /\ (in_shadow_of (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) a -> a < S (ar_sptop ar)).
Hypothesis FFRS0 : CHA.ffrs FFrest sp0.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> CHA.sclientA L ar LBrest FFrest sp0 d a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CHA.in_reg E0 r a -> exists w, In w Wo /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.
Variable CPS : list CC.cutpoint.
Variable K : ShapeAlg.TSet.
Variable FPI : FPState -> Prop.
Hypothesis DEF0 : L5.defined M0 (sp0 - SCR) SCR.
Hypothesis DEFUP : L5.defined M0 sp0 (ar_stack_top ar - sp0).
Variable SCELLS : list (Z * Z * Z).
Variable GLO GHI : Z.
Hypothesis SCELLS_ok : incl SCELLS (asc_cells C)
  /\ Forall (fun c : Z * Z * Z => 0 <= fst (fst c) /\ fst (fst c) + snd (fst c) <= hl_img_hi L /\ 0 <= snd (fst c) <= 8) SCELLS.
Hypothesis GOT_ok : asc_got_lo C <= GLO /\ GHI <= asc_got_hi C /\ 0 <= GLO /\ GHI <= hl_img_hi L.
Variable XI : nat -> env -> list (Z * Z) -> mem -> Model -> Prop.
Hypothesis KNIL : K [].

Abbreviation AMBX := (CHA.ambX L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 XI).
Abbreviation curB := (CHA.curB LBrest BLS).
Abbreviation curF := (CHA.curF FFrest sp0 FFS).


Lemma smalloc_leaf_u2 : forall (UN : kentry -> Prop) k news i c ps j cj ci,
  In k PM_FS_CLASSES -> nth_error CPS j = Some cj ->
  CHA.custom_chk NF d SCELLS GLO GHI (hl_scr_stack_malloc L) 1 (nth i BLS []) (nth i FFS []) [] news None c ps cj (nth i BLS []) (nth i FFS []) (nth j BLS []) (nth j FFS []) = Some ci ->
  SR.ps_pc ps = hl_stack_malloc L k ->
  CHA.frames_eqb (nth j FFS []) ((EVar (CH2.ci_nx ci + 5), k, CH2.ci_csp ci) :: nth i FFS []) = true ->
  CH2.blocks_eqb (nth j BLS []) (nth i BLS []) = true ->
  (forall X, In X news -> (CHA.static_chk SCELLS GLO GHI X || CRA.smalloc_fact_ok IMGHI d (SR.ps_cells ps) (CH2.ci_nx ci) (nth i BLS []) (nth i FFS []) k (CH2.ci_nx ci + 5) (CH2.ci_nx ci) X)%bool = true \/ UN X) ->
  2 <= D0 - Z.of_nat (length (nth i FFS [])) ->
  (forall E E2 cr, Cred i E cr -> env_agree NF E E2 -> Cred j E2 cr) ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> AMBX i E A M model -> FPI fx' -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 -> CCA.IH (hl_segs L) CPS AMBX K FPI (CC.meas c E) ->
    (forall R2 M2 model2 F fl LK' cr, regs_preserved R' R2 -> getr R2 10%bv = Z_to_bv 64 F ->
        CRA.sm_facts L ar k (curB i E) (curF i E) LK' (sp0 + CH2.ci_csp ci) (hl_scr_stack_malloc L) M1 M2 F fl ->
        ri_inv HI (curB i E) ((F, k, sp0 + CH2.ci_csp ci + 32) :: curF i E) LK' cr A M2 (vml_of model2) ->
        XI j (CH2.retEx E' (CH2.ci_nx ci) [Z_to_bv 64 fl] R2) A M2 model2 /\
        (forall X, UN X -> In X news -> kentry_ok (hl_segs L) (CH2.retEx E' (CH2.ci_nx ci) [Z_to_bv 64 fl] R2) (CCA.vis A model2 M2) X)) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.
Proof.
  intros UN k news i c ps j cj ci Hk Hcj Hchk Hpc Hfeq Hbeq Hnews Hroom HCred fx' E R A M model E' R' M1 model1 HAt [HA HX] HFP Hag HLF HIH HXI.
  destruct (CHA.custom_ret L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0
              CRS_ok WRS_ok IMG_ok CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok XI (hl_scr_stack_malloc L) 1%nat (nth i BLS []) (nth i FFS []) [] news None i c ps j cj ci Hcj Hchk
              E R A M model E' R' M1 model1 HAt HA Hag HLF HIH) as [CF CONT].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  pose proof HA' as (Hmo1 & Hrt1 & HA01 & HagE & (cr & LK & HH1 & HLK1 & HC1 & HRoom1) & Hfr1 & Hdf1).
  apply CHA.frames_eqb_eq in Hfeq. apply CH2.blocks_eqb_eq in Hbeq.
  assert (CHK2 : CH2.blocks_vars_lt (CH2.ci_nx ci) (nth i BLS []) = true /\ CHA.frames_vars_lt (CH2.ci_nx ci) (nth i FFS []) = true).
  { unfold CHA.custom_chk in Hchk. destruct (CHA.common_chk NF d (hl_scr_stack_malloc L) 1 c ps cj (nth i BLS []) (nth i FFS [])) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb Z5].
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [_ Z2]. split; assumption. }
  destruct CHK2 as [BV FV].
  pose proof (CHA.rng_of_wf _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH1)) as RF1.
  destruct (CHA.rf_ceil _ _ _ _ RF1) as (CL & _). destruct (CHA.rf_sptop _ _ _ _ RF1) as (SP1 & _). pose proof Hstk as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (USP : bv_unsigned (getr R' 2%bv) = sp0 + CH2.ci_csp ci) by (rewrite Hsp; apply u64_of_Z; lia).
  rewrite Hpc.
  apply (PmHeapIfaceA.aio_stack_malloc _ _ _ _ _ HIok k Hk fx' R' M1 model1 (curB i E) (curF i E) LK cr A K HH1 (proj1 Hmo1) (proj2 Hmo1) Htp).
  - rewrite Hra. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'.
  - rewrite USP. split; [exact K1|]. split; [lia|]. split; [lia|]. split; [exact K4|]. split; [|exact K6].
    intros dd m Hdd Hm. exact (L5C.writable_of_defined (hl_segs L) M1 _ _ K5 ltac:(lia) ltac:(lia) dd m Hdd Hm).
  - unfold ff_room. specialize (HRoom1 k Hk). lia.
  - rewrite USP. exact Hffrs.
  - exact KNIL.
  - rewrite USP. intros R2 M2 model2 F fl LK' Ha0 HRP Q1 Q2 Q3 Q4 HLK' Q5 Q6 Q7 Q8 Q9 Qst Q10 HPres Hrt2 HMI2 HH2. rewrite Hra.
    assert (Hmo2 : CHA.amodel_ok A model2) by (split; [rewrite (L5LZ.model_rt_halted _ _ Hrt2); exact (proj1 Hmo1) | exact HMI2]).
    set (nx := CH2.ci_nx ci) in *. set (E2 := CH2.retEx E' nx [Z_to_bv 64 fl] R2).
    pose proof (CH2.retEx_agree E' nx [Z_to_bv 64 fl] R2 : env_agree nx E' E2) as Hag2.
    assert (HagEE2 : env_agree NF E E2).
    { eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact V4]|]. eapply CC.env_agree_le; [exact Hag2 | lia]. }
    assert (FR : 0 <= F < 2 ^ 64) by (destruct Q1 as (G1 & G2 & _ & (G0 & _) & G5); pose proof (CHA.frame_class_facts k Hk); lia).
    assert (HvF : CL5A.uv E2 (EVar (nx + 5)) = F).
    { unfold CL5A.uv. cbn [edenot]. pose proof (CH2.retEx_a0 E' nx [Z_to_bv 64 fl] R2) as G. cbn [length] in G. replace (nx + 1 + 4)%nat with (nx + 5)%nat in G by lia.
      unfold E2. rewrite G, Ha0. apply u64_of_Z. exact FR. }
    assert (Hvfl : CL5A.uv E2 (EVar nx) = fl).
    { unfold CL5A.uv. cbn [edenot]. pose proof (CH2.retEx_ghost E' nx [Z_to_bv 64 fl] R2 0 ltac:(cbn; lia)) as G. rewrite Nat.add_0_r in G. cbn [nth] in G.
      unfold E2. rewrite G. apply u64_of_Z. destruct (CHA.rf_fs _ _ _ _ RF1) as ((G0 & _) & G3 & _). unfold FS_BYTES in *. lia. }
    assert (HBj : curB j E2 = curB i E).
    { unfold CHA.curB. rewrite Hbeq. rewrite (CH2.den_agree nx E' E2 _ Hag2 BV), HdenB. reflexivity. }
    assert (HFj : curF j E2 = (F, k, sp0 + CH2.ci_csp ci + 32) :: curF i E).
    { unfold CHA.curF. rewrite Hfeq. unfold CHA.denF at 1. cbn [map fst snd app]. fold (CHA.denF sp0 E2 (nth i FFS [])).
      unfold CL5A.uv in HvF. rewrite HvF. rewrite (CHA.denF_agree sp0 nx E' E2 _ Hag2 FV), HdenF. reflexivity. }
    apply (CONT fx' R2 A M2 model2 [Z_to_bv 64 fl] (curB i E) (curF i E) [] eq_refl HFP (CH2.regs_preserved_kept R' R2 HRP) I (CHA.ahpres_of_aheap_pres _ _ _ _ _ _ _ _ HPres)).
    + unfold CHA.curB. rewrite HdenB. apply incl_refl.
    + unfold CHA.curF. rewrite HdenF. apply incl_refl.
    + intros w a [].
    + split.
      * apply (CHA.amb_callee L ar C HI HIok NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 STK SCR_pos NF32 i j E E2 A A M1 M2 model1 model2
                 (CH2.ci_csp ci) (hl_scr_stack_malloc L) (curB i E) (curF i E) [] cr LK' HA' (CHA.ahpres_of_aheap_pres _ _ _ _ _ _ _ _ HPres)).
        -- unfold CHA.curB. apply incl_appr, incl_refl.
        -- unfold CHA.curF. apply incl_appr, incl_refl.
        -- exact Hc1.
        -- exact Hs0.
        -- exact Hc2.
        -- intros w a [].
        -- exact Hrt2.
        -- exact Hmo2.
        -- apply incl_refl.
        -- rewrite HBj, HFj. exact HH2.
        -- exact (incl_tran HLK' HLK1).
        -- exact HagEE2.
        -- exact (HCred E E2 cr HC1 HagEE2).
        -- rewrite HFj, Hfeq. cbn [length]. pose proof (CHA.wf_nodup _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2)) as [_ ND].
           pose proof (CHA.ffroom_push NF 0 NF32 _ _ _ (F, k, sp0 + CH2.ci_csp ci + 32) _ HRoom1 HLK' ND) as G.
           replace (D0 - Z.of_nat (Datatypes.S (length (nth i FFS [])))) with (D0 - Z.of_nat (length (nth i FFS [])) - 1) by lia. exact G.
      * apply (proj1 (HXI R2 M2 model2 F fl LK' cr HRP Ha0 ltac:(constructor; assumption) HH2)).
    + assert (SMF : CRA.sm_facts L ar k (curB i E) (curF i E) LK' (sp0 + CH2.ci_csp ci) (hl_scr_stack_malloc L) M1 M2 F fl) by (constructor; assumption).
      intros X HXn _. destruct (Hnews X HXn) as [Hnews'|Hu]; [|exact (proj2 (HXI R2 M2 model2 F fl LK' cr HRP Ha0 SMF HH2) X Hu HXn)]. apply orb_prop in Hnews' as [Hs|Hs].
      * exact (CHA.static_sound L ar C HI HIok LY_img NF 0 NF32 SCELLS GLO GHI SCELLS_ok GOT_ok _ _ _ _ _ _ _ E2 X HH2 Hs).
      * apply (CRA.smalloc_fact_sound L ar C HI HIok LY_img IMGHI LY_imghi NF E0 LBrest FFrest sp0 d Wo STK SCR_pos NF32 SP0 Wo_ok CRS_ok WRS_ok E' E2 nx (SR.ps_cells ps) (nth i BLS []) (nth i FFS []) k (nx + 5)%nat nx M1 M2 A A model1 model2 (curB i E) (curF i E) LK LK' cr F fl (sp0 + CH2.ci_csp ci + 32)
                 HagE' Hag2 HK HH1); try assumption.
        -- unfold CHA.curB. rewrite HdenB. reflexivity.
        -- unfold CHA.curF. rewrite HdenF. reflexivity.
Qed.
End Inst.
End ESMK.
