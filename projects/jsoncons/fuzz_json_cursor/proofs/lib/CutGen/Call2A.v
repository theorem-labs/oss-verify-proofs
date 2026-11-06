(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CB2.
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

Abbreviation AAMB := (CHA.aamb L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0).
Abbreviation AMBX := (CHA.ambX L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 XI).
Abbreviation curB := (CHA.curB LBrest BLS).
Abbreviation curF := (CHA.curF FFrest sp0 FFS).
Abbreviation CFACTS := (CHA.common_facts L ar HI NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0).

Lemma callee_leaf2 : forall pc scr dc ng1 BLk1 wregs1 news1 a0x1 ng2 BLk2 wregs2 news2 a0x2 i c ps j1 cj1 ci1 j2 cj2 ci2,
  nth_error CPS j1 = Some cj1 -> nth_error CPS j2 = Some cj2 ->
  CHA.custom_chk NF d SCELLS GLO GHI scr ng1 BLk1 (nth i FFS []) wregs1 news1 a0x1 c ps cj1 (nth i BLS []) (nth i FFS []) (nth j1 BLS []) (nth j1 FFS []) = Some ci1 ->
  CHA.custom_chk NF d SCELLS GLO GHI scr ng2 BLk2 (nth i FFS []) wregs2 news2 a0x2 c ps cj2 (nth i BLS []) (nth i FFS []) (nth j2 BLS []) (nth j2 FFS []) = Some ci2 ->
  CC.cp_pc cj2 = CC.cp_pc cj1 -> CH2.ci_csp ci2 = CH2.ci_csp ci1 ->
  SR.ps_pc ps = pc ->
  CHA.frames_eqb (nth j1 FFS []) (nth i FFS []) = true -> CHA.frames_eqb (nth j2 FFS []) (nth i FFS []) = true ->
  dc <= D0 - Z.of_nat (length (nth i FFS [])) ->
  forall (fx' : FPState) E R A M model E' R' M1 model1,
    CCA.AtV (hl_segs L) c E R A M model -> AMBX i E A M model -> FPI fx' -> env_agree (CC.cp_nx c) E E' ->
    CCA.leaf_factsA (hl_segs L) c ps E' R' A M model M1 model1 -> CCA.IH (hl_segs L) CPS AMBX K FPI (CC.meas c E) ->
    (forall cr LK,
       CFACTS scr ng1 c ps cj1 ci1 i E E' R' A M1 model1 ->
       ri_inv HI (curB i E) (curF i E) LK cr A M1 (vml_of model1) -> incl LK LK0 -> Cred i E cr ->
       exists (Pre : bvmap 5 word -> mem -> Prop)
              (Post : bvmap 5 word -> mem -> bvmap 5 word -> mem -> list (Z * Z) -> credit -> list (Z * Z) -> list L5.range -> Prop),
       CBA.cps_asanG L ar HI FPI pc (CC.cp_pc cj1) (sp0 + CH2.ci_csp ci1) scr (curB i E) (curF i E) LK cr A dc Pre Post
       /\ Pre R' M1
       /\ forall R2 M2 model2 LB' cr' LBk Wc LK2 A2,
            Post R' M1 R2 M2 LB' cr' LBk Wc -> regs_preserved R' R2 ->
            CHA.ahpres L ar LBk (curF i E) (sp0 + CH2.ci_csp ci1) scr Wc M1 M2 ->
            model_rt model1 model2 -> incl A A2 -> CHA.amodel_ok A2 model2 -> incl LK2 LK ->
            ri_inv HI LB' (curF i E) LK2 cr' A2 M2 (vml_of model2) ->
            (exists ghosts, length ghosts = ng1 /\
              let E2 := CH2.retEx E' (CH2.ci_nx ci1) ghosts R2 in
              match a0x1 with Some e => getr R2 10%bv = edenot E2 e | None => True end /\
              incl (CH2.den E' BLk1 ++ LBrest) LBk /\
              (forall w a, In w Wc -> L5.in_rng w a -> exists r, In r wregs1 /\ CHA.in_reg E' r a) /\
              (forall w a, In w Wc -> L5.in_rng w a -> ~ CHA.akept L ar LBrest FFrest sp0 SCR W a) /\
              ri_inv HI (curB j1 E2) (curF i E) LK2 cr' A2 M2 (vml_of model2) /\ Cred j1 E2 cr' /\ XI j1 E2 A2 M2 model2 /\
              (forall X, In X news1 -> In X (CC.cp_know cj1) -> kentry_ok (hl_segs L) E2 (CCA.vis A2 model2 M2) X))
            \/
            (exists ghosts, length ghosts = ng2 /\
              let E2 := CH2.retEx E' (CH2.ci_nx ci2) ghosts R2 in
              match a0x2 with Some e => getr R2 10%bv = edenot E2 e | None => True end /\
              incl (CH2.den E' BLk2 ++ LBrest) LBk /\
              (forall w a, In w Wc -> L5.in_rng w a -> exists r, In r wregs2 /\ CHA.in_reg E' r a) /\
              (forall w a, In w Wc -> L5.in_rng w a -> ~ CHA.akept L ar LBrest FFrest sp0 SCR W a) /\
              ri_inv HI (curB j2 E2) (curF i E) LK2 cr' A2 M2 (vml_of model2) /\ Cred j2 E2 cr' /\ XI j2 E2 A2 M2 model2 /\
              (forall X, In X news2 -> In X (CC.cp_know cj2) -> kentry_ok (hl_segs L) E2 (CCA.vis A2 model2 M2) X))) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M1 (seg_rom (hl_segs L))) model1) K.
Proof.
  intros pc scr dc ng1 BLk1 wregs1 news1 a0x1 ng2 BLk2 wregs2 news2 a0x2 i c ps j1 cj1 ci1 j2 cj2 ci2 Hcj1 Hcj2 Hchk1 Hchk2 Hpc12 Hcsp Hpc Hfeq1 Hfeq2 Hdc
         fx' E R A M model E' R' M1 model1 HAt [HA HX] HFP Hag HLF HIH USER.
  destruct (CHA.custom_ret L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0
              CRS_ok WRS_ok IMG_ok CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok XI scr ng1 BLk1 (nth i FFS []) wregs1 news1 a0x1 i c ps j1 cj1 ci1 Hcj1 Hchk1
              E R A M model E' R' M1 model1 HAt HA Hag HLF HIH) as [CF CONT1].
  destruct (CHA.custom_ret L ar C HI HIok LY_img LY_ro NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W Wo BLS FFS Cred D0 STK SCR_pos NF32 SP0 TP0 Wo_incl Wo_ok FFRS0
              CRS_ok WRS_ok IMG_ok CPS K FPI DEF0 DEFUP SCELLS GLO GHI SCELLS_ok GOT_ok XI scr ng2 BLk2 (nth i FFS []) wregs2 news2 a0x2 i c ps j2 cj2 ci2 Hcj2 Hchk2
              E R A M model E' R' M1 model1 HAt HA Hag HLF HIH) as [CF2 CONT2].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' (HdenB & HdenF) Hffrs Hmeas].
  pose proof CF2 as [_ _ _ (W1 & W2 & W3 & W4 & W5) _ _ _ _ _ _ (HdenB2 & HdenF2) _ _].
  pose proof HA' as (Hmo1 & Hrt1 & HA01 & HagE & (cr & LK & HH1 & HLK1 & HC1 & HRoom1) & Hfr1 & Hdf1).
  destruct (USER cr LK CF HH1 HLK1 HC1) as (Pre & Post & SPEC & HPre & HPost).
  apply CHA.frames_eqb_eq in Hfeq1, Hfeq2.
  assert (FVgen : forall ci cj ng BLk wregs news a0x BLj FLj, CHA.custom_chk NF d SCELLS GLO GHI scr ng BLk (nth i FFS []) wregs news a0x c ps cj (nth i BLS []) (nth i FFS []) BLj FLj = Some ci ->
                  CHA.frames_vars_lt (CH2.ci_nx ci) (nth i FFS []) = true).
  { intros ci cj ng BLk wregs news a0x BLj FLj Hchk. unfold CHA.custom_chk in Hchk. destruct (CHA.common_chk NF d scr ng c ps cj (nth i BLS []) (nth i FFS [])) as [ci0|]; [|discriminate].
    lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection Hchk as <-.
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [_ Z5]. exact Z5. }
  pose proof (FVgen _ _ _ _ _ _ _ _ _ Hchk1) as FV1. pose proof (FVgen _ _ _ _ _ _ _ _ _ Hchk2) as FV2.
  rewrite Hpc.
  apply (SPEC fx' R' M1 model1 K HH1 Hmo1 KNIL HFP Hra Hraok Hsp Htp Hstk); [apply (CHA.ffroom_le _ _ _ _ HRoom1); exact Hdc | exact Hffrs | exact HPre |].
  intros fx2 R2 M2 model2 LB' cr' LBk Wc LK2 A2 HFP2 HPo HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
  destruct (HPost R2 M2 model2 LB' cr' LBk Wc LK2 A2 HPo HRP HP Hrt2 HA2 Hmo2 HLK2 HH2)
    as [(ghosts & Hlen & Ha0 & HiB & HWr & HWk & HHj & HCj & HXj & Hnews) | (ghosts & Hlen & Ha0 & HiB & HWr & HWk & HHj & HCj & HXj & Hnews)].
  - set (E2 := CH2.retEx E' (CH2.ci_nx ci1) ghosts R2) in *.
    pose proof (CH2.retEx_agree E' (CH2.ci_nx ci1) ghosts R2 : env_agree (CH2.ci_nx ci1) E' E2) as Hag2.
    assert (HFj : curF j1 E2 = curF i E).
    { unfold CHA.curF. rewrite Hfeq1. rewrite (CHA.denF_agree sp0 _ E' E2 _ Hag2 FV1). rewrite HdenF. reflexivity. }
    assert (HagEE2 : env_agree NF E E2).
    { eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact V4]|]. eapply CC.env_agree_le; [exact Hag2 | lia]. }
    apply (CONT1 fx2 R2 A2 M2 model2 ghosts LBk (curF i E) Wc Hlen HFP2 (CH2.regs_preserved_kept R' R2 HRP) Ha0 HP HiB).
    + unfold CHA.curF. rewrite HdenF. apply incl_refl.
    + exact HWr.
    + split; [|exact HXj].
      apply (CHA.amb_callee L ar C HI HIok NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 STK SCR_pos NF32 i j1 E E2 A A2 M1 M2 model1 model2
               (CH2.ci_csp ci1) scr LBk (curF i E) Wc cr' LK2 HA' HP).
      * intros b Hb. apply HiB. apply in_or_app. right. exact Hb.
      * unfold CHA.curF. apply incl_appr, incl_refl.
      * exact Hc1.
      * exact Hs0.
      * exact Hc2.
      * exact HWk.
      * exact Hrt2.
      * exact Hmo2.
      * exact HA2.
      * rewrite HFj. exact HHj.
      * exact (incl_tran HLK2 HLK1).
      * exact HagEE2.
      * exact HCj.
      * rewrite HFj, Hfeq1.
        pose proof (CHA.wf_nodup _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHj)) as [_ ND].
        exact (CHA.ffroom_sub NF 0 NF32 _ _ _ _ HRoom1 HLK2 ND).
    + exact Hnews.
  - set (E2 := CH2.retEx E' (CH2.ci_nx ci2) ghosts R2) in *.
    pose proof (CH2.retEx_agree E' (CH2.ci_nx ci2) ghosts R2 : env_agree (CH2.ci_nx ci2) E' E2) as Hag2.
    assert (HFj : curF j2 E2 = curF i E).
    { unfold CHA.curF. rewrite Hfeq2. rewrite (CHA.denF_agree sp0 _ E' E2 _ Hag2 FV2). rewrite HdenF2. reflexivity. }
    assert (HagEE2 : env_agree NF E E2).
    { eapply CC.env_agree_trans; [eapply CC.env_agree_le; [exact Hag | exact W4]|]. eapply CC.env_agree_le; [exact Hag2 | lia]. }
    rewrite <- Hcsp in HP. rewrite <- Hpc12.
    apply (CONT2 fx2 R2 A2 M2 model2 ghosts LBk (curF i E) Wc Hlen HFP2 (CH2.regs_preserved_kept R' R2 HRP) Ha0 HP HiB).
    + unfold CHA.curF. rewrite HdenF2. apply incl_refl.
    + exact HWr.
    + split; [|exact HXj].
      apply (CHA.amb_callee L ar C HI HIok NF E0 M0 model0 A0 LBrest FFrest LK0 sp0 d W BLS FFS Cred D0 STK SCR_pos NF32 i j2 E E2 A A2 M1 M2 model1 model2
               (CH2.ci_csp ci2) scr LBk (curF i E) Wc cr' LK2 HA' HP).
      * intros b Hb. apply HiB. apply in_or_app. right. exact Hb.
      * unfold CHA.curF. apply incl_appr, incl_refl.
      * rewrite Hcsp. exact Hc1.
      * exact Hs0.
      * rewrite Hcsp. exact Hc2.
      * exact HWk.
      * exact Hrt2.
      * exact Hmo2.
      * exact HA2.
      * rewrite HFj. exact HHj.
      * exact (incl_tran HLK2 HLK1).
      * exact HagEE2.
      * exact HCj.
      * rewrite HFj, Hfeq2.
        pose proof (CHA.wf_nodup _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHj)) as [_ ND].
        exact (CHA.ffroom_sub NF 0 NF32 _ _ _ _ HRoom1 HLK2 ND).
    + exact Hnews.
Qed.
End Inst.
End CB2.
