From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps SymExec3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_ContStmt LbB_Conv LbB_PrsStmt LbB_FKit LbB_Own LbB_PmBase LbB_Call LbB_Bridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_SR LbB_WoGen LbB_WoDefs LbB_WoKit LbB_PiStmt LbB_PiInit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRepFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BllocRep BG_Free6.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoBP LbB_PmExit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DiagStmt LbB_WoDiagP LbB_WoKit2 LbB_WoDiagF LbB_PmMagW LbB_PmHTK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoDiagC.
Import ListNotations.

#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WDB.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Lemma bp_meas : forall (w : piw H) LB LBs m c, bp_pp H w LB LBs m c -> bp_phc (pc_state c) (pw_words H w) (pw_n H w) ->
    0 <= pw_n H w -> pm_meas_ok (pw_n H w) LBs.
  Proof.
    intros w LB LBs m c (PR & PSH & HC & HU & HD & (SO1 & SO2) & OWN & CW) PH Hn.
    pose proof (bp_phc_blocks _ _ _ PH) as SB.
    pose proof SO2 as SO2'. rewrite SB in SO2'.
    unfold pm_meas_ok. rewrite lb_small_lbl, nlarge_lbl, <- length_lbl.
    rewrite (fold_perm _ _ _ SO2'), (fold_perm (fun x => nlg (snd x)) _ _ SO2'), (Permutation_length SO2').
    cbn [fold_right snd length]. unfold nsmall, nlg, po_small, po_cnt, po_large. cbn -[Z.div].
    assert (0 <= pw_n H w / 2) by (apply Z.div_pos; lia). assert (0 <= pw_n H w / 3) by (apply Z.div_pos; lia). lia.
  Qed.
  Lemma wlb_small_perm : forall L L', Permutation L L' -> lb_small L = lb_small L'.
  Proof. intros L L' P. induction P; unfold lb_small in *; cbn [fold_right] in *; lia. Qed.
  Lemma wnlarge_perm : forall L L', Permutation L L' -> nlarge L = nlarge L'.
  Proof. intros L L' P. induction P; unfold nlarge in *; cbn [fold_right] in *; lia. Qed.
  Lemma wlb_small_app : forall L L', lb_small (L ++ L') = lb_small L + lb_small L'.
  Proof. intros L L'. induction L as [|b L IH]; [reflexivity|]. cbn [app]. unfold lb_small in *. cbn [fold_right]. lia. Qed.
  Lemma wnlarge_app : forall L L', nlarge (L ++ L') = nlarge L + nlarge L'.
  Proof. intros L L'. induction L as [|b L IH]; [reflexivity|]. cbn [app]. unfold nlarge in *. cbn [fold_right]. lia. Qed.
  Lemma wtb_meas : forall (TB : list block), (length TB <= 1)%nat -> lb_small TB <= 64512 /\ 0 <= nlarge TB <= 1.
  Proof.
    intros [|b [|b' TB]] HL; cbn [length] in HL; [cbn; lia | | lia].
    unfold lb_small, nlarge. cbn [fold_right]. unfold nsmall, nlg.
    destruct (Z.leb_spec (blk_size b) 64512); destruct (Z.ltb_spec 64512 (blk_size b)); lia.
  Qed.

End WDB.

Section WDC2.
  #[local] Set Default Proof Using "All".
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV_P5 ds_repA.
  Hypothesis HTR : ds_tr_ok H.
  Variable e : went H.
  Variables ff fp : Z.
  Variable mo0 : Model.
  Variable w : piw H.
  Variable c0 : parserC.
  Variable LBs : list block.
  Variable s0 : as_St H.
  Variable LB0 : list block.
  Variable m0 : mem.
  Variable XSc0 : list (Z * Z).
  Hypothesis HP : wpre H e.
  Hypothesis HWL : bp_wl H e ff w.
  Hypothesis HPP : bp_pp H w LB0 LBs m0 c0.
  Hypothesis HI0 : winv H e ff fp XSc0 s0 LB0 m0.
  Hypothesis HMD : mdef m0 (pw_p H w) PARSER_SIZE.
  Hypothesis HAL : PM_RESERVE <= as_AL H s0.
  Hypothesis HMEAS : pm_meas_ok (pw_n H w) LBs.

  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.

  Local Abbreviation wsr := (LbB_WoDiagC.wsr H ds_repA e ff fp mo0 w c0 LBs s0 LB0 m0).
  Local Abbreviation wxkeep := (LbB_WoDiagC.wxkeep H e ff fp LB0).
  Let wpk := LbB_WoDiagC.w_post_keep H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL.
  Let wg2 := LbB_WoDiagC.w_geo2 H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL.
  Local Abbreviation LF6 := ((6, ff, fp) :: w_LF e) (only parsing).

  Lemma w_bud : forall DB LB, Permutation LB (DB ++ LB0) -> (length DB <= 1)%nat ->
    lb_small LB + 3 * 64512 <= RT_SMALL_MAX /\ Z.of_nat (length LB) + 2 <= RT_CNT_MAX /\ nlarge LB + 2 <= RT_LARGE_MAX.
  Proof.
    intros DB LB PM DL.
    pose proof HPP as (_ & _ & _ & _ & _ & (SO1 & _) & _).
    pose proof HWL as (_ & _ & _ & Wn & WLB & _).
    rewrite WLB in SO1.
    pose proof HP as (_ & _ & _ & _ & _ & B1 & B2 & B3 & _).
    pose proof HMEAS as (M1 & M2 & M3). rewrite Wn in M1, M2, M3.
    assert (P2 : Permutation LB (DB ++ w_LB e ++ LBs)) by (eapply Permutation_trans; [exact PM | apply Permutation_app_head; exact SO1]).
    rewrite (wlb_small_perm _ _ P2), (wnlarge_perm _ _ P2), (Permutation_length P2), !wlb_small_app, !wnlarge_app, !length_app.
    destruct (wtb_meas DB DL) as [T1 T2].
    unfold RT_SMALL_MAX, RT_CNT_MAX, RT_LARGE_MAX in *. lia.
  Qed.

  Ltac wkin := solve [cbn [In WD_KEEP WD_MKEEP]; repeat (first [left; reflexivity | right])].

  Lemma w_rc_keep : forall R R', bp_rc H e ff R -> (forall r, In r WD_KEEP -> getr R' r = getr R r) -> bp_rc H e ff R'.
  Proof.
    intros R R' (C2 & C3 & C4 & C8 & C9 & C19 & C20) K.
    unfold bp_rc. rewrite !K by wkin. repeat split; assumption.
  Qed.

  Lemma w_memset : forall (Q : config -> Prop) (REGS REGS' : bvmap 5 word -> Prop) S (P P' : mem -> Prop) spent c
      (ret a v n : Z) (junk : list byte),
    wsr AASAN_MEMSET REGS S P spent c ->
    (forall R, REGS R -> getr R 1 = wz ret /\ getr R 10 = wz a /\ getr R 11 = wz v /\ getr R 12 = wz n) ->
    ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    0 <= v < 256 -> 0 <= n <= 2 ^ 40 -> bp_flw H e ff (a, a + n) -> wfree S (a, a + n) -> a + n <= w_lo e ->
    ff <= a -> a + n <= ff + WO_FLAGP -> wfree S (wS1 e - AINTRIN_STACK, wS1 e) ->
    (forall m, P m -> rw_cells asegs m a [CB (Z.to_nat n) junk] /\ accessible m a n /\ shvis m a (a + n)) ->
    (forall R R', REGS R -> (forall r, In r WD_MKEEP -> getr R' r = getr R r) -> REGS' R') ->
    (forall m m', P m -> munch [(a, a + n); (wS1 e - AINTRIN_STACK, wS1 e)] m m' -> wmono asegs m m' ->
       rw_cells asegs m' a [CB (Z.to_nat n) (poison_bytes (Z.to_nat n) v)] -> P' m') ->
    (forall c', wsr ret REGS' S P' spent c' -> as_SR H Q c') ->
    as_SR H Q c.
  Proof.
    intros Q REGS REGS' S P P' spent [msF mo] ret a v n junk
      (s & R & F & fc & m & XSc & LB & KR & MP & VIS & RF & FZ & HI & SL & RC & RG & AG & OWN & SES & HPm & AL)
      RGS Hr2 Hr Hv Hn FLW FRa Hlo Ha1 Ha2 FRs OBJ KREG KP K.
    cbn [cfg_ms cfg_model] in *.
    destruct (RGS R RG) as (G1 & G10 & G11 & G12).
    assert (G1' : getr R 1 = Z_to_bv 64 ret) by exact G1.
    destruct (OBJ m HPm) as (CJ & ACC & SHV).
    pose proof RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
    pose proof (wpre_geo H e HP) as (CE & _ & _ & _ & _ & _).
    pose proof (wS1_facts H e HP) as (_ & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wframe_bounds H e ff fp _ _ _ _ HP HI) as (B0 & _ & B1 & B2 & B3 & B4 & _ & B6 & B7 & B8 & B9 & B10).
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI))
      as (F1 & F2 & _ & F4 & F5 & F6 & F7 & F8 & F9 & F10 & _ & _ & _ & _ & _ & _).
    pose proof aceil_facts as ACF.
    pose proof HI as (RFS & FF & RH & AC & MI & S0 & RAX & ER & ST & _).
    assert (Ua : bv_unsigned (getr R 10) = a) by (rewrite G10; unfold wz; apply unsigned_lit; lia).
    assert (Un : bv_unsigned (getr R 12) = n) by (rewrite G12; unfold wz; apply unsigned_lit; lia).
    assert (Us1 : bv_unsigned (getr R 2) = wS1 e) by (rewrite C2; unfold wz; apply unsigned_lit; lia).
    destruct (stk_split asegs m (w_lo e) (wS1 e) (wSP e) ST ltac:(lia)) as [STl STu].
    rewrite (rfull_eq R RF) in VIS.
    eapply (ahh_evt_then H HH _ Q s msF _ mo KR VIS).
    - apply (ah_memset H HH (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31) F fc m v junk (w_lo e)).
      + exact G11.
      + exact Hv.
      + rewrite Ua, Un. exact CJ.
      + rewrite Ua, Un. exact ACC.
      + rewrite Ua, Un. exact SHV.
      + rewrite Us1. exact STl.
      + exact CE.
      + rewrite Us1. unfold AINTRIN_STACK. lia.
      + exact MI.
      + exact AC.
      + rewrite Un. lia.
      + rewrite Ua, Un. eapply aapp_in_app_mem; [exact F10 | lia | unfold WO_FLAGP in *; lia].
      + rewrite Ua, Un. eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact F10 | cbn; lia | cbn; unfold WO_FLAGP in *; lia].
      + rewrite Ua, Un. left. exact Hlo.
    - intros msF' mo' KR' MP'
        (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & VIS' & MU & WM & MI' & STK' & RC' & AC').
      rewrite Ua, Un, Us1 in MU. rewrite Us1 in STK'. rewrite Ua, Un in RC'.
      rewrite G1', (ret_pc_even ret Hr Hr2) in VIS'.
      pose proof (stk_merge asegs m' (w_lo e) (wS1 e) (wSP e) STK' (stk_wmono m m' (wS1 e) (wSP e) STu WM ltac:(lia)) ltac:(lia)) as ST'.
      assert (FW : Forall (bp_flw H e ff) [(a, a + n); (wS1 e - AINTRIN_STACK, wS1 e)]).
      { apply Forall_cons; [exact FLW|]. apply Forall_cons; [| apply Forall_nil].
        unfold bp_flw; cbn [fst snd]. unfold WO_FLAGP, AINTRIN_STACK in *.
        split; [right; right; split; lia|]. repeat split; right; lia. }
      assert (FS : Forall (wfree S) [(a, a + n); (wS1 e - AINTRIN_STACK, wS1 e)])
        by (apply Forall_cons; [exact FRa | apply Forall_cons; [exact FRs | apply Forall_nil]]).
      assert (FWW : Forall (wwin H e ff) [(a, a + n); (wS1 e - AINTRIN_STACK, wS1 e)]).
      { apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; unfold wwin; cbn [fst snd].
        - right; left. split; lia.
        - left. unfold WO_SAVED, AINTRIN_STACK in *. split; lia. }
      pose proof (winv_munch H HH e ff fp XSc s LB m m' _ HP HI MU WM MI' ST' FWW) as HI'.
      set (R' := mkR (Z_to_bv 64 ret) (getr R 2) (getr R 3) (getr R 4) t0' t1' t2' (getr R 8) (getr R 9) (getr R 10)
                     a1' a2' a3' a4' a5' a6' a7' (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23)
                     (getr R 24) (getr R 25) (getr R 26) (getr R 27) t3' t4' t5' t6').
      assert (KEEP : forall r, In r WD_MKEEP -> getr R' r = getr R r).
      { intros r Hr0. cbn [In WD_MKEEP] in Hr0.
        repeat (destruct Hr0 as [<-|Hr0]; [subst R'; first [reflexivity | cbn; rewrite G1'; reflexivity]|]). destruct Hr0. }
      assert (KEEPk : forall r, In r WD_KEEP -> getr R' r = getr R r).
      { intros r Hr0. apply KEEP. cbn [In WD_KEEP WD_MKEEP] in Hr0 |- *. tauto. }
      apply K. exists s, R', F, fc, m', XSc, LB.
      split; [exact KR'|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP')|]. split; [exact VIS'|].
      split; [apply rfull_mkR|]. split; [exact FZ|]. split; [exact HI'|].
      split; [exact (LbB_WoDiagC.w_slots_munch H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL m m' _ SL MU WM FW)|].
      split; [exact (w_rc_keep R R' RC KEEPk)|]. split; [exact (KREG R R' RG KEEP)|].
      split; [exact (LbB_WoDiagC.w_pf_munch H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL m m' _ AG MU FW)|].
      split; [exact (lb_own_wmono _ _ _ OWN WM)|].
      split; [exact (LbB_WoDiagC.w_ses_munch H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL S XSc s LB m m' _ HI SES MU WM FW FS)|].
      split; [exact (KP m m' HPm MU WM RC')|]. exact AL.
  Qed.

  Lemma w_ctor : ds_ctor_stmtA H LINV_P5 ds_repA ->
    forall (Q : config -> Prop) (REGS REGS' : bvmap 5 word -> Prop) (P P' : mem -> Prop) spent c
      (ret ds ppos pcons pstr pstr2 err : Z),
    wsr ADS_CTOR REGS None P spent c ->
    (forall R, REGS R -> getr R 1 = wz ret /\ getr R 10 = wz ds /\ getr R 11 = wz ppos /\ getr R 12 = wz pcons
       /\ getr R 13 = wz pstr /\ getr R 14 = wz (err mod 2 ^ 64) /\ getr R 15 = wz pstr2) ->
    ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 -> spent <= PM_RESERVE -> - 2 ^ 31 <= err < 0 ->
    ff + 8 <= ds -> ds + DS_SIZE <= ff + 3376 ->
    (forall m, P m -> exists (pos : list word) (j1 j2 : list byte),
       ds_obj H LF6 m (wS1 e) ds DS_SIZE /\ wr_at asegs m ds DS_SIZE /\ obj_inframe LF6 ds DS_SIZE
       /\ ds_obj H LF6 m (wS1 e) ppos 24 /\ u64arr asegs m ppos pos /\ length pos = 3%nat /\ obj_inframe LF6 ppos 24
       /\ ds_obj H LF6 m (wS1 e) pstr 24 /\ rw_cells asegs m pstr [C2 (Z_to_bv 64 0); CB 22 j1] /\ obj_inframe LF6 pstr 24
       /\ ds_obj H LF6 m (wS1 e) pstr2 24 /\ rw_cells asegs m pstr2 [C2 (Z_to_bv 64 0); CB 22 j2] /\ obj_inframe LF6 pstr2 24
       /\ ds_obj H LF6 m (wS1 e) pcons 48 /\ rw_cells asegs m (pcons + 32) [C8 (Z_to_bv 64 0)]
       /\ (forall a, ds <= a < ds + DS_SIZE -> ~ (ppos <= a < ppos + 24) /\ ~ (pstr <= a < pstr + 24)
                                             /\ ~ (pstr2 <= a < pstr2 + 24) /\ ~ (pcons <= a < pcons + 48))) ->
    (forall R R', REGS R -> (forall r, In r WD_KEEP -> getr R' r = getr R r) -> REGS' R') ->
    (forall m m', P m -> wxkeep [(ds, ds + DS_SIZE)] m m' -> P' m') ->
    (forall c', wsr ret REGS' (Some (ds, err, 0)) P' spent c' -> as_SR H Q c') ->
    as_SR H Q c.
  Proof.
    intros HCTOR Q REGS REGS' P P' spent [msF mo] ret ds ppos pcons pstr pstr2 err
      (s & R & F & fc & m & XSc & LB & KR & MP & VIS & RF & FZ & HI & SL & RC & RG & AG & OWN & SES & HPm & AL)
      RGS Hr2 Hr Hsp Herr Hd1 Hd2 OBJ KREG KP K.
    cbn [cfg_ms cfg_model wses] in *.
    destruct (RGS R RG) as (G1 & G10 & G11 & G12 & G13 & G14 & G15).
    assert (G1' : getr R 1 = Z_to_bv 64 ret) by exact G1.
    destruct (OBJ m HPm) as (pos & j1 & j2 & O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13 & O14 & O15 & O16).
    pose proof RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
    destruct (w_bud [] LB SES (le_0_n 1)) as (BU1 & BU2 & BU3).
    pose proof HPP as (_ & _ & _ & _ & _ & (SO1 & _) & _).
    pose proof HWL as (_ & _ & _ & _ & WLB & _).
    rewrite WLB in SO1.
    pose proof wg2 as (GE1 & GE2 & GE3).
    pose proof (wframe_bounds H e ff fp _ _ _ _ HP HI) as (B0 & B64 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    assert (Us1 : bv_unsigned (getr R 2) = wS1 e) by (rewrite C2; unfold wz; apply unsigned_lit; lia).
    assert (RAE : bv_unsigned (getr R 1) mod 2 = 0) by (rewrite G1'; rewrite unsigned_lit by lia; exact Hr2).
    rewrite (rfull_eq R RF) in VIS.
    destruct (wd_pre H HH e ff fp XSc s LB m msF mo ADS_CTOR
                (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9) (getr R 10)
                (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 19)
                (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28)
                (getr R 29) (getr R 30) (getr R 31) F fc [] 0 HTR HP HI KR VIS FZ C2 C8 C4 RAE (lb_own_nil m)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (errv & DP).
    eapply (ah_seq H HH).
    { eapply (HCTOR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s LB LF6
                ((wSP e, bv_unsigned (w_ra e)) :: w_CH e) (w_lo e) (w_B e) (w_shi e) errv ds ppos pcons pstr pstr2 err pos j1 j2 DP).
      - exact G10.
      - exact G11.
      - exact G12.
      - exact G13.
      - exact G14.
      - exact G15.
      - exact Herr.
      - rewrite Us1. exact O1.
      - exact O2.
      - exact O3.
      - rewrite Us1. exact O4.
      - exact O5.
      - exact O6.
      - exact O7.
      - rewrite Us1. exact O8.
      - exact O9.
      - exact O10.
      - rewrite Us1. exact O11.
      - exact O12.
      - exact O13.
      - rewrite Us1. exact O14.
      - exact O15.
      - exact O16. }
    intros c' POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & LB1
                      & XS & F1 & fc1 & VIS1 & FZ1 & RES & KR1 & MP1 & MI1 & STK1 & ERR1 & RA1 & RH1 & QC1 & FXS & XP
                      & RFS1 & AC1 & S01 & LI1 & AL1).
    destruct QC1 as (PM1 & REP1 & WR1).
    rewrite Us1 in STK1, XP. rewrite C4 in ERR1.
    rewrite G1', (ret_pc_even ret Hr Hr2) in VIS1.
    assert (INC0 : forall b, In b LB0 -> In b LB) by (intros b Hb; exact (Permutation_in _ (Permutation_sym SES) Hb)).
    assert (INC : forall b, In b (w_LB e) -> In b LB).
    { intros b Hb. apply INC0. apply (Permutation_in _ (Permutation_sym SO1)). apply in_or_app. left. exact Hb. }
    assert (XC : Forall (fun iv : Z * Z => (ff + 8 <= fst iv /\ snd iv <= ff + WO_FLAGP /\ wr_at asegs m1 (fst iv) (snd iv - fst iv))
                                       \/ iv = (RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)) [(ds, ds + DS_SIZE)]).
    { apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. replace (ds + DS_SIZE - ds) with DS_SIZE by lia.
      unfold WO_FLAGP, DS_SIZE in *. split; [lia|]. split; [lia|]. exact WR1. }
    pose proof (wd_back H HH e ff fp XSc s LB m LB [(ds, ds + DS_SIZE)] XS s1 LB1 m1 errv1 HP HI INC XP FXS XC RFS1 RH1 AC1 MI1
                  STK1 ERR1 RA1 LI1) as HI1.
    assert (XO : Forall (wxok ff) [(ds, ds + DS_SIZE)]).
    { apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold WO_FLAGP, DS_SIZE in *. lia. }
    destruct (wpk LB [(ds, ds + DS_SIZE)] XS m m1 INC0 XO FXS XP SL AG OWN) as (SL1 & AG1 & OWN1).
    set (R' := mkR (Z_to_bv 64 ret) (getr R 2) (getr R 3) (getr R 4) t0' t1' t2' (getr R 8) (getr R 9) a0' a1' a2' a3' a4' a5' a6' a7'
                   (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26)
                   (getr R 27) t3' t4' t5' t6').
    assert (KEEP : forall r, In r WD_KEEP -> getr R' r = getr R r).
    { intros r Hr0. cbn [In WD_KEEP] in Hr0.
      repeat (destruct Hr0 as [<-|Hr0]; [subst R'; first [reflexivity | cbn; rewrite G1'; reflexivity]|]). destruct Hr0. }
    apply K. exists s1, R', F1, fc1, m1, (XSc ++ XS), LB1.
    split; [exact KR1|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP1)|]. split; [exact VIS1|].
    split; [apply rfull_mkR|]. split; [exact FZ1|]. split; [exact HI1|].
    split; [exact SL1|]. split; [exact (w_rc_keep R R' RC KEEP)|]. split; [exact (KREG R R' RG KEEP)|].
    split; [exact AG1|]. split; [exact OWN1|].
    split; [exists []; split; [exact REP1|]; split; [exact (Permutation_trans PM1 SES) | apply lb_own_nil]|].
    split; [exact (KP m m1 HPm (ex_intro _ LB (ex_intro _ XS (conj INC0 (conj FXS XP)))))|].
    lia.
  Qed.

  Lemma w_cseq : put_cseq_stmtA H LINV_P5 ds_repA ->
    forall (Q : config -> Prop) (REGS REGS' : bvmap 5 word -> Prop) (P P' : mem -> Prop) spent c (ret ds err len p n : Z),
    wsr APUT_CSEQ REGS (Some (ds, err, len)) P spent c ->
    (forall R, REGS R -> getr R 1 = wz ret /\ getr R 10 = wz ds /\ getr R 11 = wz p /\ getr R 12 = wz n) ->
    ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 -> spent + ds_cost (len + n) <= PM_RESERVE ->
    ff + 8 <= ds -> ds + DS_SIZE <= ff + 3376 ->
    (forall m, P m -> ds_obj H LF6 m (wS1 e) ds DS_SIZE /\ obj_inframe LF6 ds DS_SIZE) ->
    0 <= n -> AIMG_LO + 64 <= p -> p + n + 64 <= AIMG_TOP ->
    (forall m', ACONST m' -> accessible m' p n) ->
    (exists bs, length bs = Z.to_nat n /\ forall m', mem_inv asegs m' -> bytes_at asegs m' p bs) ->
    len + n <= 1024 ->
    (forall R R', REGS R -> (forall r, In r WD_KEEP -> getr R' r = getr R r) -> getr R' 10 = wz ds -> REGS' R') ->
    (forall m m', P m -> wxkeep [(ds, ds + DS_SIZE)] m m' -> P' m') ->
    (forall c', wsr ret REGS' (Some (ds, err, len + n)) P' (spent + ds_cost (len + n)) c' -> as_SR H Q c') ->
    as_SR H Q c.
Proof.
    intros HCSEQ Q REGS REGS' P P' spent [msF mo] ret ds err len p n
      (s & R & F & fc & m & XSc & LB & KR & MP & VIS & RF & FZ & WI & SL & RC & RG & AG & OWNs & (DB & REP & PM & OWN) & PP & AL)
      RR Hr2 Hr Hsp Hds1 Hds2 OBJ Hn Hp0 Hp ACC BYT Hlen KREG KP K.
    cbn [cfg_ms cfg_model] in *.
    destruct (RR R RG) as (G1 & G10 & G11 & G12).
    pose proof RC as (G2 & G3 & G4 & G8 & G9 & G19 & G20).
    pose proof (dla_blocks _ _ DSL LB m ds err len DB REP) as (DL & _).
    destruct (w_bud DB LB PM DL) as (B1 & B2 & B3).
    destruct (OBJ m PP) as (OBd & IFd).
    pose proof WI as (RFS & FR & RH & AC & MI & S0 & RA & (errv0 & ER) & ST & _).
    pose proof (wframe_facts H _ _ _ FR) as (FF1 & FF2 & FF3 & FF4 & FF5 & FF6 & FF7 & FF8 & _).
    pose proof (LbB_WoDiagC.w_geo H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL XSc s LB m WI) as (_ & _ & GF1 & GF2 & GS1 & GS2 & _).
    assert (WLB : forall b, In b (w_LB e) -> In b LB0).
    { intros b Hb. pose proof HPP as (_ & _ & _ & _ & _ & (SO & _) & _). pose proof HWL as (_ & _ & _ & _ & HL0 & _).
      rewrite HL0 in SO. apply (Permutation_in _ (Permutation_sym SO)). apply in_or_app; left; exact Hb. }
    assert (Us1 : bv_unsigned (getr R 2) = wS1 e) by (rewrite G2; unfold wz; apply unsigned_lit; lia).
    assert (Hra : bv_unsigned (getr R 1) mod 2 = 0) by (rewrite G1; unfold wz; rewrite unsigned_lit by lia; exact Hr2).
    rewrite (rfull_eq R RF) in VIS.
    destruct (wd_pre H HH e ff fp XSc s LB m msF mo APUT_CSEQ
                (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9) (getr R 10)
                (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 19) (getr R 20)
                (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30)
                (getr R 31) F fc DB (ds_cost (len + n)) HTR HP WI KR VIS FZ G2 G8 G4 Hra OWN ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (errv & DP).
    eapply (ah_seq H HH).
    { eapply (HCSEQ (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9) (getr R 10)
                (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 19) (getr R 20)
                (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30)
                (getr R 31) F fc msF m mo s LB LB0 LF6 ((wSP e, bv_unsigned (w_ra e)) :: w_CH e) (w_lo e) (w_B e) (w_shi e) errv ds err len p n DB).
      all: try lazymatch goal with |- 0 < ?p \/ ?n = 0 => left; unfold AIMG_LO in *; lia end.
      - exact DP.
      - exact G10.
      - exact G11.
      - exact G12.
      - exact REP.
      - exact PM.
      - rewrite Us1. exact OBd.
      - exact IFd.
      - exact Hn.
      - destruct BYT as (bs & LEN & BYT'). exists bs. split; [exact LEN|]. intros m' XS. intros.
        lazymatch goal with ACm : ACONST m', MIm : mem_inv asegs m' |- _ =>
          split; [exact (BYT' m' MIm)|]; split; [exact (ACC m' ACm)|]; eapply ACONST_shvis; [exact ACm | lia | lia | lia] end.
      - unfold in_app_mem, ASHADOW_BASE, AIMG_TOP, AIMG_LO in *. left. lia.
      - rewrite Us1. left. unfold ADS_STACK, AIMG_TOP in *. lia.
      - intros a Ha. split.
        + unfold AIMG_TOP in *. lia.
        + intros (b & Hb & Hr0). assert (HbL : In b LB) by (apply (Permutation_in _ (Permutation_sym PM)); apply in_or_app; left; exact Hb).
          pose proof (ah_blocks H HH _ _ _ _ RH HbL) as (_ & _ & _ & BT & _). unfold AIMG_TOP in *. lia.
      - unfold DS_MAXLEN. lia.
      - lia.
      - lia. }
    intros c' POST.
    destruct POST as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & s' & LB' & XS & F' & fc'
                      & VIS' & FZ' & RES & KR' & MP' & MI' & ST' & ER' & RA' & RH' & (B' & XF & REP' & OWN' & WR') & SCR & XP' & RFS' & AC' & S0' & LV' & AL').
    rewrite Us1 in ST', XP'. rewrite G4 in ER'.
    assert (WI' : winv H e ff fp (XSc ++ XS) s' LB' m').
    { eapply (wd_back H HH e ff fp XSc s LB m LB0 [(ds, ds + DS_SIZE)] XS s' LB' m' errv'); try eassumption.
      apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. split; [lia|]. split; [unfold WO_FLAGP; lia|].
      replace (ds + DS_SIZE - ds) with DS_SIZE by lia. exact WR'. }
    pose proof (LbB_WoDiagC.w_post_keep H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL LB0 [(ds, ds + DS_SIZE)] XS m m' (fun b Hb => Hb)) as WPK.
    destruct WPK as (SL' & AG' & OWNs');
      [ apply Forall_cons; [| apply Forall_nil]; unfold LbB_WoDiagC.wxok; left; cbn [fst snd]; unfold WO_FLAGP; lia
      | exact SCR | exact XP' | exact SL | exact AG | exact OWNs | ].
    apply K. exists s', (mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) t0 t1 t2 (getr R 8) (getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
                            (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                            (getr R 26) (getr R 27) t3 t4 t5 t6), F', fc', m', (XSc ++ XS), LB'.
    split; [exact KR'|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP')|].
    split; [rewrite VIS'; rewrite G1; unfold wz; rewrite ret_pc_even by (first [lia | exact Hr2]); reflexivity|].
    split; [apply rfull_mkR|]. split; [exact FZ'|]. split; [exact WI'|]. split; [exact SL'|].
    split; [unfold bp_rc; cbn [getr mkR PropExec.getr Vector.nth]; repeat split; assumption|].
    split; [apply (KREG R); [exact RG | intros r Hk; unfold WD_KEEP in Hk; cbn in Hk;
                              repeat (destruct Hk as [<- | Hk]; [reflexivity |]); destruct Hk
                            | cbn [getr mkR PropExec.getr Vector.nth]; exact (RES ds eq_refl)]|].
    split; [exact AG'|]. split; [exact OWNs'|].
    split; [exists B'; split; [exact REP'|]; split; [|exact OWN'];
            destruct XF as (LR & P1 & P2);
            assert (PL : Permutation LR LB0) by (apply (Permutation_app_inv_l DB); exact (Permutation_trans (Permutation_sym P1) PM));
            exact (Permutation_trans P2 (Permutation_app_head B' PL))|].
    split; [apply (KP m m' PP); exists LB0, XS; split; [intros b Hb; exact Hb|]; split; [exact SCR | exact XP']|].
    lia.
  Qed.

  Lemma w_num : forall entry lo_x hi_x enc, put_num_stmtA H LINV_P5 ds_repA entry lo_x hi_x enc ->
    forall (Q : config -> Prop) (REGS REGS' : bvmap 5 word -> Prop) (P P' : mem -> Prop) spent c (ret ds err len x : Z),
    wsr entry REGS (Some (ds, err, len)) P spent c ->
    (forall R, REGS R -> getr R 1 = wz ret /\ getr R 10 = wz ds /\ getr R 11 = wz (enc x)) ->
    ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 -> spent + ds_cost (len + 24) <= PM_RESERVE -> lo_x <= x < hi_x ->
    ff + 8 <= ds -> ds + DS_SIZE <= ff + 3376 ->
    (forall m, P m -> ds_obj H LF6 m (wS1 e) ds DS_SIZE /\ obj_inframe LF6 ds DS_SIZE) ->
    len + 24 <= 1024 ->
    (forall R R', REGS R -> (forall r, In r WD_KEEP -> getr R' r = getr R r) -> getr R' 10 = wz ds -> REGS' R') ->
    (forall m m', P m -> wxkeep [(ds, ds + DS_SIZE); (RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)] m m' -> P' m') ->
    (forall c', wsr ret REGS' (Some (ds, err, len + 24)) P' (spent + ds_cost (len + 24)) c' -> as_SR H Q c') ->
    as_SR H Q c.
Proof.
    intros entry lo_x hi_x enc HNUM Q REGS REGS' P P' spent [msF mo] ret ds err len x
      (s & R & F & fc & m & XSc & LB & KR & MP & VIS & RF & FZ & WI & SL & RC & RG & AG & OWNs & (DB & REP & PM & OWN) & PP & AL)
      RR Hr2 Hr Hsp Hx Hds1 Hds2 OBJ Hlen KREG KP K.
    cbn [cfg_ms cfg_model] in *.
    destruct (RR R RG) as (G1 & G10 & G11).
    pose proof RC as (G2 & G3 & G4 & G8 & G9 & G19 & G20).
    pose proof (dla_blocks _ _ DSL LB m ds err len DB REP) as (DL & _).
    destruct (w_bud DB LB PM DL) as (B1 & B2 & B3).
    destruct (OBJ m PP) as (OBd & IFd).
    pose proof WI as (RFS & FR & RH & AC & MI & S0 & RA & (errv0 & ER) & ST & _).
    pose proof (wframe_facts H _ _ _ FR) as (FF1 & FF2 & FF3 & FF4 & FF5 & FF6 & FF7 & FF8 & _).
    pose proof (LbB_WoDiagC.w_geo H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL XSc s LB m WI) as (_ & _ & GF1 & GF2 & GS1 & GS2 & _).
    assert (WLB : forall b, In b (w_LB e) -> In b LB0).
    { intros b Hb. pose proof HPP as (_ & _ & _ & _ & _ & (SO & _) & _). pose proof HWL as (_ & _ & _ & _ & HL0 & _).
      rewrite HL0 in SO. apply (Permutation_in _ (Permutation_sym SO)). apply in_or_app; left; exact Hb. }
    assert (Us1 : bv_unsigned (getr R 2) = wS1 e) by (rewrite G2; unfold wz; apply unsigned_lit; lia).
    assert (Hra : bv_unsigned (getr R 1) mod 2 = 0) by (rewrite G1; unfold wz; rewrite unsigned_lit by lia; exact Hr2).
    rewrite (rfull_eq R RF) in VIS.
    destruct (wd_pre H HH e ff fp XSc s LB m msF mo entry
                (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9) (getr R 10)
                (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 19) (getr R 20)
                (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30)
                (getr R 31) F fc DB (ds_cost (len + 24)) HTR HP WI KR VIS FZ G2 G8 G4 Hra OWN ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
      as (errv & DP).
    eapply (ah_seq H HH).
    { eapply (HNUM (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9) (getr R 10)
                (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 19) (getr R 20)
                (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30)
                (getr R 31) F fc msF m mo s LB LB0 LF6 ((wSP e, bv_unsigned (w_ra e)) :: w_CH e) (w_lo e) (w_B e) (w_shi e) errv ds err len x DB).
      - exact DP.
      - exact G10.
      - exact G11.
      - exact Hx.
      - exact REP.
      - exact PM.
      - rewrite Us1. exact OBd.
      - exact IFd.
      - unfold DS_MAXLEN. lia.
      - lia.
      - lia. }
    intros c' POST.
    destruct POST as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & errv' & s' & LB' & XS & F' & fc'
                      & VIS' & FZ' & RES & KR' & MP' & MI' & ST' & ER' & RA' & RH' & (B' & XF & REP' & OWN' & WR') & SCR & XP' & RFS' & AC' & S0' & LV' & AL').
    rewrite Us1 in ST', XP'. rewrite G4 in ER'.
    assert (WI' : winv H e ff fp (XSc ++ XS) s' LB' m').
    { eapply (wd_back H HH e ff fp XSc s LB m LB0 [(ds, ds + DS_SIZE); (RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)] XS s' LB' m' errv'); try eassumption.
      apply Forall_cons; [| apply Forall_cons; [right; reflexivity | apply Forall_nil]]. left. cbn [fst snd]. split; [lia|].
      split; [unfold WO_FLAGP; lia|]. replace (ds + DS_SIZE - ds) with DS_SIZE by lia. exact WR'. }
    pose proof (LbB_WoDiagC.w_post_keep H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL LB0 [(ds, ds + DS_SIZE); (RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)] XS m m' (fun b Hb => Hb)) as WPK.
    destruct WPK as (SL' & AG' & OWNs');
      [ apply Forall_cons; [| apply Forall_cons; [unfold LbB_WoDiagC.wxok; right; reflexivity | apply Forall_nil]];
        unfold LbB_WoDiagC.wxok; left; cbn [fst snd]; unfold WO_FLAGP; lia
      | exact SCR | exact XP' | exact SL | exact AG | exact OWNs | ].
    apply K. exists s', (mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) t0 t1 t2 (getr R 8) (getr R 9) a0 a1 a2 a3 a4 a5 a6 a7
                            (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25)
                            (getr R 26) (getr R 27) t3 t4 t5 t6), F', fc', m', (XSc ++ XS), LB'.
    split; [exact KR'|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP')|].
    split; [rewrite VIS'; rewrite G1; unfold wz; rewrite ret_pc_even by (first [lia | exact Hr2]); reflexivity|].
    split; [apply rfull_mkR|]. split; [exact FZ'|]. split; [exact WI'|]. split; [exact SL'|].
    split; [unfold bp_rc; cbn [getr mkR PropExec.getr Vector.nth]; repeat split; assumption|].
    split; [apply (KREG R); [exact RG | intros r Hk; unfold WD_KEEP in Hk; cbn in Hk;
                              repeat (destruct Hk as [<- | Hk]; [reflexivity |]); destruct Hk
                            | cbn [getr mkR PropExec.getr Vector.nth]; exact (RES ds eq_refl)]|].
    split; [exact AG'|]. split; [exact OWNs'|].
    split; [exists B'; split; [exact REP'|]; split; [|exact OWN'];
            destruct XF as (LR & P1 & P2);
            assert (PL : Permutation LR LB0) by (apply (Permutation_app_inv_l DB); exact (Permutation_trans (Permutation_sym P1) PM));
            exact (Permutation_trans P2 (Permutation_app_head B' PL))|].
    split; [apply (KP m m' PP); exists LB0, XS; split; [intros b Hb; exact Hb|]; split; [exact SCR | exact XP']|].
    lia.
  Qed.

  Lemma w_dtor : ds_dtor_stmtA H LINV_P5 ds_repA ->
    forall (Q : config -> Prop) (REGS REGS' : bvmap 5 word -> Prop) (P P' : mem -> Prop) spent c (ret ds err len : Z),
    wsr ADS_DTOR REGS (Some (ds, err, len)) P spent c ->
    (forall R, REGS R -> getr R 1 = wz ret /\ getr R 10 = wz ds) ->
    ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 -> spent <= PM_RESERVE -> In (APC0_FREE, [0xfd148; ret]) PO_PF ->
    ff + 8 <= ds -> ds + DS_SIZE <= ff + 3376 ->
    (forall m, P m -> ds_obj H LF6 m (wS1 e) ds DS_SIZE /\ obj_inframe LF6 ds DS_SIZE) ->
    (forall R R', REGS R -> (forall r, In r WD_KEEP -> getr R' r = getr R r) -> REGS' R') ->
    (forall m m', P m -> wxkeep [(ds, ds + DS_SIZE)] m m' -> P' m') ->
    (forall c', wsr ret REGS' None P' spent c' -> as_SR H Q c') ->
    as_SR H Q c.
  Proof.
    intros HDTOR Q REGS REGS' P P' spent [msF mo] ret ds err len
      (s & R & F & fc & m & XSc & LB & KR & MP & VIS & RF & FZ & HI & SL & RC & RG & AG & OWN & SES & HPm & AL)
      RGS Hr2 Hr Hsp PF Hd1 Hd2 OBJ KREG KP K.
    cbn [cfg_ms cfg_model wses] in *.
    destruct SES as (DB & REP & PM & DOWN).
    destruct (RGS R RG) as (G1 & G10).
    assert (G1' : getr R 1 = Z_to_bv 64 ret) by exact G1.
    destruct (OBJ m HPm) as (OBd & IFd).
    pose proof RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
    pose proof (proj1 (dla_blocks _ _ DSL LB m ds err len DB REP)) as DL.
    destruct (w_bud DB LB PM DL) as (BU1 & BU2 & BU3).
    pose proof HPP as (_ & _ & _ & _ & _ & (SO1 & _) & _).
    pose proof HWL as (_ & _ & _ & _ & WLB & _).
    rewrite WLB in SO1.
    pose proof wg2 as (GE1 & GE2 & GE3).
    pose proof (wframe_bounds H e ff fp _ _ _ _ HP HI) as (B0 & B64 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
    assert (Us1 : bv_unsigned (getr R 2) = wS1 e) by (rewrite C2; unfold wz; apply unsigned_lit; lia).
    assert (RAE : bv_unsigned (getr R 1) mod 2 = 0) by (rewrite G1'; rewrite unsigned_lit by lia; exact Hr2).
    rewrite (rfull_eq R RF) in VIS.
    destruct (wd_pre H HH e ff fp XSc s LB m msF mo ADS_DTOR
                (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9) (getr R 10)
                (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 19)
                (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28)
                (getr R 29) (getr R 30) (getr R 31) F fc DB 0 HTR HP HI KR VIS FZ C2 C8 C4 RAE DOWN
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (errv & DP).
    eapply (ah_seq H HH).
    { eapply (HDTOR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s LB LB0 LF6
                ((wSP e, bv_unsigned (w_ra e)) :: w_CH e) (w_lo e) (w_B e) (w_shi e) errv ds err len DB DP).
      - rewrite G1', unsigned_lit by lia. exact (wd_dtor_pf H e ret HP PF).
      - exact G10.
      - exact REP.
      - exact PM.
      - rewrite Us1. exact OBd.
      - exact IFd. }
    intros c' POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & LB1
                      & XS & F1 & fc1 & VIS1 & FZ1 & RES & KR1 & MP1 & MI1 & STK1 & ERR1 & RA1 & RH1 & QC1 & FXS & XP
                      & RFS1 & AC1 & S01 & LI1 & AL1).
    destruct QC1 as (PM1 & AD1 & WR1).
    rewrite Us1 in STK1, XP. rewrite C4 in ERR1.
    rewrite G1', (ret_pc_even ret Hr Hr2) in VIS1.
    assert (INC : forall b, In b (w_LB e) -> In b LB0).
    { intros b Hb. apply (Permutation_in _ (Permutation_sym SO1)). apply in_or_app. left. exact Hb. }
    assert (XC : Forall (fun iv : Z * Z => (ff + 8 <= fst iv /\ snd iv <= ff + WO_FLAGP /\ wr_at asegs m1 (fst iv) (snd iv - fst iv))
                                       \/ iv = (RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)) [(ds, ds + DS_SIZE)]).
    { apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. replace (ds + DS_SIZE - ds) with DS_SIZE by lia.
      unfold WO_FLAGP, DS_SIZE in *. split; [lia|]. split; [lia|]. exact WR1. }
    pose proof (wd_back H HH e ff fp XSc s LB m LB0 [(ds, ds + DS_SIZE)] XS s1 LB1 m1 errv1 HP HI INC XP FXS XC RFS1 RH1 AC1 MI1
                  STK1 ERR1 RA1 LI1) as HI1.
    assert (XO : Forall (wxok ff) [(ds, ds + DS_SIZE)]).
    { apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold WO_FLAGP, DS_SIZE in *. lia. }
    destruct (wpk LB0 [(ds, ds + DS_SIZE)] XS m m1 (fun b Hb => Hb) XO FXS XP SL AG OWN) as (SL1 & AG1 & OWN1).
    set (R' := mkR (Z_to_bv 64 ret) (getr R 2) (getr R 3) (getr R 4) t0' t1' t2' (getr R 8) (getr R 9) a0' a1' a2' a3' a4' a5' a6' a7'
                   (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26)
                   (getr R 27) t3' t4' t5' t6').
    assert (KEEP : forall r, In r WD_KEEP -> getr R' r = getr R r).
    { intros r Hr0. cbn [In WD_KEEP] in Hr0.
      repeat (destruct Hr0 as [<-|Hr0]; [subst R'; first [reflexivity | cbn; rewrite G1'; reflexivity]|]). destruct Hr0. }
    apply K. exists s1, R', F1, fc1, m1, (XSc ++ XS), LB1.
    split; [exact KR1|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP1)|]. split; [exact VIS1|].
    split; [apply rfull_mkR|]. split; [exact FZ1|]. split; [exact HI1|].
    split; [exact SL1|]. split; [exact (w_rc_keep R R' RC KEEP)|]. split; [exact (KREG R R' RG KEEP)|].
    split; [exact AG1|]. split; [exact OWN1|]. split; [exact PM1|].
    split; [exact (KP m m1 HPm (ex_intro _ LB0 (ex_intro _ XS (conj (fun b Hb => Hb) (conj FXS XP)))))|].
    lia.
  Qed.

End WDC2.
