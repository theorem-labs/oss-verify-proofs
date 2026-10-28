From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface BsWalk.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PiStmt LbB_PiExit LbB_RwKit LbB_PiInit LbB_HStKit LbB_DKit LbB_HKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmLH LbB_DStat LbB_WoDefs LbB_WoKit LbB_WoKit2 LbB_WoBP.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
Import ListNotations.
Open Scope Z_scope.

#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma lwo_wr_of_mdef : forall M a n, mdef M a n -> AIMG_TOP <= a -> a + n <= 2 ^ 64 -> wr_at asegs M a n.
Proof.
  intros M a n HD Ha Hn. split; [unfold AIMG_TOP in Ha; lia|]. split; [lia|]. intros i Hi.
  pose proof (HD i Hi) as Di.
  unfold wa. rewrite BakeStackRep.wview_high by (rewrite unsigned_lit by (unfold AIMG_TOP in Ha; lia); lia).
  destruct (M (Z_to_bv 64 (a + i))) as [b|] eqn:E; [discriminate | contradiction].
Qed.

Section LoopWo.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Hypothesis PI : parse_inst_stmtB H LINV_P5.
  Hypothesis HTR : pm_tr_ok H.

  Lemma bp_loop_wo : forall e ff fp Q mo0, bp_klexit H e ff fp Q mo0 -> bp_kloop H e ff fp Q mo0.
  Proof.
    intros e ff fp Q mo0 KX s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP WP WI SL SH RC RG WL PR.
    pose proof (proj1 HHbp) as HH.
    destruct PR as (ee & K0 & PP & HDR & AL & BIN & CC0).
    destruct PP as (PRp & PSH & HC & HU & HD & SOWN & LBOWN & CWR).
    destruct AL as (AL1 & AL2 & AL3).
    destruct RC as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
    destruct RG as (R18 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
    pose proof WL as WL'. destruct WL' as (Wp & Wc & Ww & Wn & WLB & Ws0 & Wlo & WB & Wshi).
    pose proof (wpre_geo H e WP) as (G1 & G2 & G3 & G4 & G5 & G6).
    pose proof (wS1_facts H e WP) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof (bp_fr_of_winv H e ff fp XSc s LB m WI) as [BF WRP].
    pose proof WI as WI'.
    destruct WI' as (WRFS & WFF & WRH & WAC & WMI & WS0 & WRA & WERR & WSTK & WSV & WFL & WW1 & WW2 & WXP & WXS & WLI).
    assert (RA_EQ : AWO_PM_RA = BP_RA) by reflexivity.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (Hsp : bv_unsigned (PropExec.getr R 2) = wS1 e) by (rewrite R2; apply u64_of_Z; unfold AAPP_HI in *; lia).
    assert (Hs0 : bv_unsigned (PropExec.getr R 8) = wSP e) by (rewrite R8; reflexivity).
    destruct (wchain_call H HH e ff fp XSc s LB m WP WI) as [CHN CHR].
    pose proof (wpm_pf H e WP) as HPF. rewrite RA_EQ in HPF.
    assert (FR0 : bp_frl H e ff fp m) by (exists XSc; split; [exact BF | split; [exact SL | exact SH]]).
    assert (FRK : forall m0 m' XS, bp_frl H e ff fp m0 -> Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS ->
        xpres H (pw_LB0 H w) (bv_unsigned (PropExec.getr R 2)) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: (pw_p H w, pw_p H w + PARSER_SIZE) :: XS) m0 m' ->
        stk asegs m' (pw_lo H w) (bv_unsigned (PropExec.getr R 2)) -> as_RFS H ((6, ff, fp) :: w_LF e) m' -> bp_frl H e ff fp m').
    { intros m0 m' XS F0 FX XP ST RS. rewrite Hsp in XP, ST. exact (bp_frl_keep H HH e ff fp w WP WL m0 m' XS F0 FX XP ST RS). }
    rewrite (rfull_eq R RF) in VIS. rewrite R18, <- Wp in VIS.
    eapply (bp_entry H HHbp LINV_P5 PI w ((6, ff, fp) :: w_LF e) ((wSP e, bv_unsigned (w_ra e)) :: w_CH e)
              (PropExec.getr R 2) (PropExec.getr R 3) (PropExec.getr R 4) (PropExec.getr R 8) (PropExec.getr R 9) (PropExec.getr R 19) (PropExec.getr R 20) (PropExec.getr R 21) (PropExec.getr R 22) (PropExec.getr R 23)
              (PropExec.getr R 25) (PropExec.getr R 26) (PropExec.getr R 27) (bp_frl H e ff fp) FRK).
    - rewrite R4. exact G6.
    - rewrite Hsp. clear - S1. Z.div_mod_to_equations. lia.
    - rewrite Hsp, WB. pose proof WP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & WPB & _). unfold wSP in *. lia.
    - rewrite Hsp, Wshi. lia.
    - rewrite Wlo. exact G1.
    - rewrite Hsp, Wlo. unfold APM_STACK. lia.
    - pose proof WP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WPL & _).
      cbn [length]. unfold PM_FRAMES, PO_FRAMES in *. lia.
    - exact HPF.
    - intros fp' ra' Hin. rewrite Hsp. exact (CHR fp' ra' Hin).
    - exact HTR.
    - intros m0 m' W L0 MU WM FW. eapply LINV_P5_cl; [exact L0|]. intros a Ha Hc. unfold wa. apply MU.
      rewrite unsigned_lit by exact Ha.
      apply (disjoint_outside W a 1); [| lia].
      assert (AT : a + 1 <= AIMG_TOP) by (unfold aimg_client in Hc; unfold AIMG_TOP; lia).
      clear - FW AT. induction W as [|[lo hi] W IH]; cbn; [exact I|].
      inversion FW as [|iv W' Hiv FW']; subst. cbn in Hiv. split; [lia | apply IH; exact FW'].
    - intros s1 LB1 LBs1 m1 mo1 msF1 ra1 t01 t11 t21 a01 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61 F1 fc1 r
             VIS1 Hr FZ1 KR1 MP1 [c' PE] K1 FR1 STK1 RFS1 CHN1.
      destruct FR1 as (XSc1 & BF1 & SL1 & SH1).
      pose proof PE as PE'.
      destruct PE' as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22).
      pose proof (wframe_facts H _ _ _ WFF) as (FF1 & FF2 & FF3 & FF4).
      eapply (KX s1 LB1 LBs1 m1 mo1 msF1 _ F1 fc1 XSc1 w r).
      + exact VIS1.
      + apply rfull_mkR.
      + exact FZ1.
      + exact KR1.
      + exact MP1.
      + exact WP.
      + eapply winv_of_bp_fr; [exact BF1 | | exact E1 | exact E18 | exact E15 | | | | exact E20].
        * rewrite Wp in E22. apply lwo_wr_of_mdef; [exact E22 | unfold AIMG_TOP in *; lia | unfold PARSER_SIZE; lia].
        * rewrite <- Wlo, <- Wshi. exact E19.
        * rewrite <- WB. exact E17.
        * rewrite G6. exact E16.
      + exact SL1.
      + exact SH1.
      + repeat split; [exact R2 | exact R3 | exact R4 | exact R8 | exact R9 | exact R19 | exact R20].
      + split; [exact R22 | exact R23].
      + reflexivity.
      + exact Hr.
      + exact WL.
      + exists c'. exact PE.
    - exact VIS.
    - exact FZ.
    - exact KR.
    - exact MP.
    - exact K0.
    - exact PRp.
    - exact PSH.
    - exact HC.
    - exact HU.
    - exact HD.
    - exact HDR.
    - exact SOWN.
    - exact LBOWN.
    - exact WRH.
    - exact WMI.
    - rewrite R4 in *. rewrite <- G6. exact WERR.
    - rewrite WB. exact WRA.
    - exact WAC.
    - rewrite Wlo, Wshi. exact WS0.
    - exact WLI.
    - exact CWR.
    - destruct BIN as (_ & _ & BW & BN). rewrite Ww. exact BW.
    - destruct BIN as (_ & _ & BW & BN). rewrite Wn. exact BN.
    - exact AL1.
    - exact AL2.
    - exact AL3.
    - exact FR0.
    - rewrite Hsp, Wlo. destruct (stk_split asegs m (w_lo e) (wS1 e) (wSP e) WSTK ltac:(lia)) as [ST1 _]. exact ST1.
    - exact WRFS.
    - rewrite Hs0. exact CHN.
  Qed.
End LoopWo.
