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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_Conv LbB_MILB LbB_PrsStmt LbB_HKit LbB_HStKit LbB_PmExit LbB_PiStmt LbB_PiInit LbB_PmTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ContStmt LbB_RwStm LbB_PmHTK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoBP LbB_Own LbB_RwStm LbB_PmHTK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmHdr2 LbB_DStat LbB_DiagStmt LbB_PmBMRS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmHex LbB_PmBMRS LbB_PmBMT LbB_WoDiagP LbB_WoDiagC LbB_WoDiagC2 LbB_WoShK LbB_PmMagK LbB_PmMagW LbB_PmHdr2 LbB_HdrGetP LbB_ContV4 LbB_WoKit LbB_WoKit3 LbB_PmBMT3.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma t2_ext : forall x, 0 <= x < 2 ^ 32 -> wz (ext_Z true 0 4 x) = wz (sx32 x).
Proof.
  intros x Hx. unfold ext_Z. cbv beta zeta iota.
  change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
  change (8 * N.of_nat 4)%N with 32%N.
  rewrite Z.div_1_r, Z.mod_small by lia. unfold wz. exact (swrap32_sx32 x Hx).
Qed.

Lemma t2_fld_ro8 : forall m a z, ro_cells asegs m a [C8 (Z_to_bv 64 z)] -> 0 <= a -> fldA m a 8 z.
Proof.
  intros m a z Hc Ha. unfold fldA, fld.
  pose proof (ro_cells_read asegs m a _ 0%nat _ Hc eq_refl) as RD. replace (a + Z.of_nat 0) with a in RD by lia.
  rewrite <- rdn_of_ov. exact RD.
Qed.

Ltac t2kin := solve [cbn [In WD_KEEP WD_MKEEP]; repeat (first [left; reflexivity | right])].
Ltac t2splits := repeat match goal with |- _ /\ _ => split end.

Section BMT2.
  #[local] Set Default Proof Using "All".
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV_P5 ds_repA.
  Hypothesis HTR : ds_tr_ok H.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV_P5 ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV_P5 ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV_P5 ds_repA.
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
  Hypothesis HPF : bp_pfresh H w s0 LB0 LBs m0 c0.
  Hypothesis HW : w_words e <> 0.
  Hypothesis HN : 5 <= w_n e.


  Lemma t2_obj : forall m m', bp_shad ff [14; 15; 20; 21]%nat m' ->
    ds_obj H ((6, ff, fp) :: w_LF e) m (wS1 e) (ff + 1760) DS_SIZE ->
    ds_obj H ((6, ff, fp) :: w_LF e) m' (wS1 e) (ff + 1760) DS_SIZE.
  Proof.
    intros m m' SH (_ & O2 & O3 & O4 & O5 & O6 & O7).
    pose proof (hdr_geo H e ff fp XSc0 s0 LB0 m0 HP HI0) as (G1 & G2 & _).
    split; [| exact (conj O2 (conj O3 (conj O4 (conj O5 (conj O6 O7)))))].
    apply (bp_shad_addr ff [14; 15; 20; 21]%nat m' 1760 DS_SIZE SH).
    - lia.
    - clear - G1. Z.div_mod_to_equations. lia.
    - lia.
    - reflexivity.
    - unfold DS_SIZE. lia.
    - reflexivity.
    - vm_compute. discriminate.
    - vm_compute. reflexivity.
  Qed.

  Lemma t2_keep : forall X m m', bm_mid_mem H e ff fp m -> wxkeep H e ff fp LB0 X m m' ->
    Forall (fun iv : Z * Z => sh ff + 512 <= fst iv \/ snd iv <= sh ff) X -> bm_mid_mem H e ff fp m'.
  Proof.
    intros X m m' (SH & O & I) K FX.
    pose proof (rt_bp_base H HHbp) as HH.
    pose proof HI0 as (RF & FF & _).
    pose proof (wframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof (wpre_geo H e HP) as (CE & _).
    destruct K as (LBk & XS & INC & FS & XP).
    assert (SH' : bp_shad ff [14; 15; 20; 21]%nat m').
    { unfold bp_shad in *. eapply xpres_u8arr; [exact XP | exact SH |].
      rewrite length_map. replace (Z.of_nat (length (wo_sh [14; 15; 20; 21]%nat))) with 476 by (vm_compute; reflexivity).
      split; [right; right; right; right; right; left; lia |].
      apply Forall_app. split.
      - eapply Forall_impl; [| exact FX]. intros iv Kv. cbn beta in Kv. lia.
      - eapply Forall_impl; [| exact FS]. intros iv FSi.
        destruct (wfsw_ok H HH e ff fp m0 iv RF FF CE FSi) as (_ & _ & _ & _ & _ & B6 & _). lia. }
    split; [exact SH' | split; [exact (t2_obj m m' SH' O) | exact I]].
  Qed.

  Lemma pm_bm_t2 : forall (Q : config -> Prop), bp_kmagf H e ff fp Q mo0 ->
    forall len spent c,
      wsr H ds_repA e ff fp mo0 w c0 LBs s0 LB0 m0 BM_MID (bm_mid_regs ff) (Some (ff + 1760, -4, len))
        (bm_mid_mem H e ff fp) spent c ->
      bm_mid_ok len spent -> as_SR H Q c.
  Proof.
    intros Q KF len spent c WS [OKL OKS].
    pose proof (rt_bp_base H HHbp) as HH.
    pose proof (hdr_geo H e ff fp XSc0 s0 LB0 m0 HP HI0) as (G01 & G02 & G03 & G04 & G05 & G06 & G07 & G08 & G09 & G010 & G011 & G012 & G013 & G014 & G015 & G016).
    assert (LEN0 : 0 <= len).
    { destruct WS as (s & R & F & fc & m & XSc & LB & KR & MP & VIS & RF & FZ & HI & SL & RC & RG & AG & OWN & SES & HPm & AL).
      destruct SES as (DB & DSR & _).
      exact (proj2 (proj2 (proj2 (proj2 (dla_def _ _ DSL LB m (ff + 1760) (-4) len DB DSR))))). }
    assert (WS' : wsr H ds_repA e ff fp mo0 w c0 LBs s0 LB0 m0 BM_MID (bm_mid_regs ff) (Some (ff + 1760, -4, len))
                    (fun m => bm_mid_mem H e ff fp m /\ fldA m (ff + 3504) 8 (w_words e)) spent c).
    { destruct WS as (s & R & F & fc & m & XSc & LB & KR & MP & VIS & RF & FZ & HI & SL & RC & RG & AG & OWN & SES & HPm & AL).
      pose proof HWL as (Wp & Wc & Ww & Wn & WLB & Ws0 & Wlo & WB & Wshi).
      pose proof HPF as (PP & FR & AL0 & CC).
      pose proof PP as (PR & PSH & HC & HU & HD & SOWN & LBOWN & CWR).
      pose proof PR as [_ _ _ _ _ Pst _ _ _ _ _ _]. destruct Pst as [W0 W1 _ _ _ _ _ _ _ _ _ _ _ _ _ _].
      pose proof FR as (PH & _). unfold pi_hdr in PH. cbn [bp_ste st_words st_nwords] in PH. destruct PH as (PW0 & PW1 & _).
      assert (F0 : fldA m0 (ff + 3504) 8 (w_words e)).
      { unfold fldA, fld. replace (ff + 3504) with (pw_p H w + ST_OFF) by (rewrite Wp; unfold ST_OFF; lia).
        rewrite <- Ww, <- PW0. exact (proj2 W0). }
      exists s, R, F, fc, m, XSc, LB.
      split; [exact KR |]. split; [exact MP |]. split; [exact VIS |]. split; [exact RF |]. split; [exact FZ |].
      split; [exact HI |]. split; [exact SL |]. split; [exact RC |]. split; [exact RG |].
      split; [exact AG |]. split; [exact OWN |]. split; [exact SES |]. split; [| exact AL].
      split; [exact HPm |].
      unfold fldA in *. apply (fld_agree ASEGS m0 m (ff + 3504) 8 (w_words e)); [lia | lia | exact F0 |].
      intros a Ha. unfold zwin in Ha. apply (AG a); [| lia]. unfold bp_pfoot, parser_foot. left. left.
      rewrite Wp. unfold PARSER_SIZE. lia. }
    apply (w_chunk_w H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL
             Q BM_MID APUT_U32 (bm_mid_regs ff)
             (fun R => getr R 1 = wz 965824 /\ getr R 10 = wz (ff + 1760)
                       /\ (exists x, 0 <= x < 2 ^ 32 /\ getr R 11 = wz (sx32 x)) /\ bm_mid_regs ff R)
             (Some (ff + 1760, -4, len)) (fun m => bm_mid_mem H e ff fp m /\ fldA m (ff + 3504) 8 (w_words e))
             (bm_mid_mem H e ff fp) spent c WS').
    - intros R F fc m XSc s LB RG RC [HPm PF] HI SL SES.
      pose proof (hdr_geo H e ff fp XSc s LB m HP HI) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
      pose proof HI as (RFS & FF & RH & AC & MI & S0 & RA & ER & ST & SV & SF & WF & WFP & XP & FS & LVI).
      destruct (hdr_words H HH e ff fp XSc s LB m HP HI HW HN) as (W16le & W16 & WHI & SHw & b0 & b1 & b2 & b3 & R0 & R1 & R2 & R3).
      pose proof HP as (_ & _ & N24 & WOK & RH0 & _).
      destruct WOK as [[E0 _] | (pw & k & Hin & Rg & W0 & _ & Whi & _)]; [contradiction |].
      destruct (blk_range H HH (w_s e) (w_LB e) (w_m e) pw (w_words e) k RH0 Hin) as (BA0 & _ & BN & _ & BAC & BAF & BAA).
      pose proof (bytes4_x b0 b1 b2 b3) as XB. cbv zeta in XB. destruct XB as (XR & _).
      pose proof (rdn4_fld m (w_words e) b0 b1 b2 b3 ltac:(lia) ltac:(lia) R0 R1 R2 R3) as FX.
      set (x := bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3) in *.
      set (q := ff / 32).
      assert (Hq : ff = 32 * q) by (subst q; clear - G1; Z.div_mod_to_equations; lia).
      assert (SHq : sh ff = 4 * q + ASHADOW_BASE).
      { unfold sh. rewrite Hq. replace (32 * q) with ((4 * q) * 8) by ring. rewrite Z.div_mul by lia. lia. }
      destruct RC as (C2 & C3 & C4 & C8 & C9 & C19 & C20).
      destruct RG as (M18 & M22 & M27).
      pose proof HPm as (SHD & OBJ & INF).
      pose proof SES as (DB & DSR & PERM & OWN).
      destruct (dla_hex _ _ DSL LB m (ff + 1760) (-4) len DB LVI AC DSR) as (vt & fl & HVT & HRO & HACC & HFL & HFLC & HREP).
      pose proof HACC as (AV0 & AV1 & _).
      assert (WL : length (wo_sh [14; 15; 20; 21]%nat) = 476%nat) by (vm_compute; reflexivity).
      assert (F235 : fldA m (4 * q + 2147451115) 1 0).
      { replace (4 * q + 2147451115) with (sh ff + Z.of_nat 235) by (rewrite SHq, ASHADOW_BASE_val; lia).
        apply (u8arr_byte0 m (sh ff) _ 235 SHD); [rewrite WL; lia | vm_compute; reflexivity]. }
      assert (FVT : fldA m (32 * q + 1760) 8 vt) by (rewrite <- Hq; exact (fld_of_rw_cells8 m (ff + 1760) vt HVT ltac:(lia))).
      assert (FVB : fldA m (vt - 24) 8 112) by exact (t2_fld_ro8 m (vt - 24) DS_VBOFF HRO ltac:(lia)).
      assert (FFL : fldA m (32 * q + 1880) 4 fl).
      { replace (32 * q + 1880) with (ff + 1760 + DS_VBOFF + 8) by (unfold DS_VBOFF; lia).
        exact (fld_of_rw_cells4 m _ fl HFLC ltac:(unfold DS_VBOFF; lia)). }
      assert (WFL : wr_at asegs m (32 * q + 1880) 4).
      { replace (32 * q + 1880) with (ff + 1760 + DS_VBOFF + 8) by (unfold DS_VBOFF; lia). exact (proj2 HFLC). }
      assert (FW : fldA m (32 * q + 3504) 8 (w_words e)) by (rewrite <- Hq; exact PF).
      assert (A18 : getr R 18 = wz ((32 * q) + 1760)) by (rewrite M18, <- Hq; reflexivity).
      assert (A19 : getr R 19 = wz ((4 * q) + ASHADOW_BASE)) by (etransitivity; [exact C19 |]; rewrite SHq; reflexivity).
      assert (A20 : getr R 20 = wz (32 * q)) by (etransitivity; [exact C20 |]; rewrite <- Hq; reflexivity).
      assert (A22 : getr R 22 = wz ((32 * q) + 3504)) by (rewrite M22, <- Hq; reflexivity).
      assert (SHV : sh0 m (vt - 24)) by exact (sh0_of_acc8 m (vt - 24) HACC).
      assert (D28 : 32 * q + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= 32 * q)
        by (rewrite <- Hq; destruct G6 as [G6|G6]; unfold aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in G6; lia).
      assert (D21 : w_words e + 4 <= 32 * q \/ 32 * q + 4096 <= w_words e) by (rewrite <- Hq; lia).
      assert (SPM : wS1 e mod 16 = 0) by (clear - G14; Z.div_mod_to_equations; lia).
      unfold AAPP_HI in AV1.
      assert (CH : exists R' M',
        CatSim.msteps asegs (MS R F (wz (0xea7c4 + 5252)) fc None m (seg_rom asegs)) (MS R' F (wz 1200700) fc None M' (seg_rom asegs))
        /\ munch [((32 * q + 1880), (32 * q + 1884))] m M' /\ wmono asegs m M' /\ fldA M' (32 * q + 1880) 4 4104
        /\ getr R' 1 = wz (0xea7c4 + 5372) /\ getr R' 2 = wz (wS1 e) /\ getr R' 10 = wz ((32 * q) + 1760)
        /\ getr R' 11 = wz (ext_Z true 0 4 x) /\ getr R' 12 = wz 4104 /\ getr R' 18 = wz ((32 * q) + 1760)
        /\ getr R' 19 = wz ((4 * q) + ASHADOW_BASE) /\ getr R' 20 = wz (32 * q) /\ getr R' 22 = wz ((32 * q) + 3504)
        /\ getr R' 27 = wz ASHADOW_BASE
        /\ (forall r, In r [3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 21; 23; 24; 25; 26; 28; 29; 30; 31]%bv -> getr R' r = getr R r)).
      { destruct HFL as [EF|EF]; rewrite EF in FFL; unfold DS_FL0, DS_FLHEX in FFL.
        - apply (bmR_ha_bp R F fc m q (wS1 e) vt (w_words e) x). unfold bmR_ha_pre. t2splits; first [assumption | lia].
        - apply (bmR_hb_bp R F fc m q (wS1 e) vt (w_words e) x). unfold bmR_hb_pre. t2splits; first [assumption | lia]. }
      destruct CH as (R' & M' & MS & MU & WM & F1880 & K1 & K2 & K10 & K11 & K12 & K18 & K19 & K20 & K22 & K27 & KEEP).
      assert (SHD' : bp_shad ff [14; 15; 20; 21]%nat M').
      { unfold bp_shad in *. eapply u8arr_transport; [exact SHD | exact MU | exact WM |].
        apply disj_of_all. intros iv [<-|[]]. cbn [fst snd]. rewrite length_map, WL. rewrite <- Hq. lia. }
      exists R', M', [((32 * q + 1880), (32 * q + 1884))].
      split; [exact MS |]. split; [exact MU |]. split; [exact WM |].
      split.
      { constructor; [| constructor]. unfold bp_flw; cbn [fst snd]. rewrite <- Hq. unfold WO_FLAGP. t2splits; lia. }
      split.
      { exists DB. split; [| split; [exact PERM | exact (lb_own_wmono _ _ _ OWN WM)]].
        apply HREP.
        - intros a Ha Hout. pose proof munch_at as MA. hinst MA H HH. apply (MA _ m M' a MU Ha).
          intros iv [<-|[]]. cbn [fst snd]. unfold DS_VBOFF in Hout. lia.
        - replace (ff + 1760 + DS_VBOFF + 8) with (32 * q + 1880) by (unfold DS_VBOFF; lia).
          apply hg_rw4; [exact F1880 | exact (wr_at_wmono _ _ _ _ WFL WM)]. }
      split.
      { split; [exact K2 |]. split; [rewrite <- C3; apply KEEP; t2kin |].
        split; [rewrite <- C4; apply KEEP; t2kin |].
        split; [rewrite <- C8; apply KEEP; t2kin |].
        split; [rewrite <- C9; apply KEEP; t2kin |].
        split; [etransitivity; [exact K19 |]; rewrite SHq; reflexivity
               | etransitivity; [exact K20 |]; rewrite <- Hq; reflexivity]. }
      split.
      { cbv beta. split; [exact K1 |]. split; [etransitivity; [exact K10 |]; rewrite <- Hq; reflexivity |]. split.
        - exists x. split; [exact XR |]. etransitivity; [exact K11 |]. exact (t2_ext x XR).
        - split; [etransitivity; [exact K18 |]; rewrite <- Hq; reflexivity |].
          split; [etransitivity; [exact K22 |]; rewrite <- Hq; reflexivity | exact K27]. }
      split; [exact SHD' | split; [exact (t2_obj m M' SHD' OBJ) | exact INF]].
    - intros c1 WS1.
      destruct WS1 as (s & R & F & fc & m & XSc & LB & KR & MP & VIS & RF & FZ & HI & SL & RC & RG & AG & OWN & SES & HPm & AL).
      destruct RG as (R1 & R10 & (x & XR & R11) & RM).
      apply (w_num H HHbp ds_repA DSL HTR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL HMEAS
               APUT_U32 0 (2 ^ 32) sx32 HU32 Q
               (fun R0 => getr R0 1 = wz 965824 /\ getr R0 10 = wz (ff + 1760) /\ getr R0 11 = wz (sx32 x) /\ bm_mid_regs ff R0)
               (bm_mid_regs ff) (bm_mid_mem H e ff fp) (bm_mid_mem H e ff fp) spent c1 965824 (ff + 1760) (-4) len x).
      + exists s, R, F, fc, m, XSc, LB.
        split; [exact KR |]. split; [exact MP |]. split; [exact VIS |]. split; [exact RF |]. split; [exact FZ |].
        split; [exact HI |]. split; [exact SL |]. split; [exact RC |].
        split; [split; [exact R1 |]; split; [exact R10 |]; split; [exact R11 | exact RM] |].
        split; [exact AG |]. split; [exact OWN |]. split; [exact SES |]. split; [exact HPm | exact AL].
      + intros R0 (A1 & A10 & A11 & _). split; [exact A1 |]. split; [exact A10 | exact A11].
      + reflexivity.
      + lia.
      + unfold ds_cost in *. lia.
      + exact XR.
      + lia.
      + unfold DS_SIZE. lia.
      + intros m1 (_ & O1 & I1). split; [exact O1 | exact I1].
      + lia.
      + intros R0 R0' (_ & _ & _ & M18 & M22 & M27) K _.
        split; [etransitivity; [apply K; t2kin | exact M18] |].
        split; [etransitivity; [apply K; t2kin | exact M22] | etransitivity; [apply K; t2kin | exact M27]].
      + intros m1 m1' HPm1 K. apply (t2_keep _ m1 m1' HPm1 K).
        pose proof (hdr_geo H e ff fp XSc0 s0 LB0 m0 HP HI0) as (_ & _ & _ & _ & _ & _ & G7 & G8 & G9 & _).
        constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold DS_SIZE, RtB_Td.ATDLOC; lia.
      + intros c2 WS2.
        apply (pm_bm_t3 H HHbp ds_repA DSL HTR HCSEQ HU32 HDTOR e ff fp mo0 w c0 LBs s0 LB0 m0 XSc0 HP HWL HPP HI0 HMD HAL
                 HMEAS HPF HW HN Q KF (len + 24) (spent + ds_cost (len + 24)) c2 WS2).
        * lia.
        * replace (len + 24 + 2) with (len + 26) by lia. exact OKS.
  Qed.
End BMT2.
