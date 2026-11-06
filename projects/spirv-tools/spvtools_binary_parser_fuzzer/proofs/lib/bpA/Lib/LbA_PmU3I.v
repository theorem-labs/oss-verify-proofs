(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Ox Require F08.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep TablFacts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmHdr LbA_PmCall LbA_PmExit2 LbA_PmGlue LbA_PmU2K LbA_PmLH LbA_PmLeaf LbA_DiagStmt LbA_PmDS LbA_ContStmt LbA_PmVops LbA_PmU2 LbA_DStat LbA_TablStmt LbA_PmOL LbA_PmPD LbA_PmSL LbA_PmWF LbA_PmU3L LbA_PmU3XK LbA_PmU3Id LbA_PmU3Ia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac inlist := cbn; repeat (first [left; reflexivity | right]).

Lemma regs_tbl_litI {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) R r z,
  PropExec.getr R r = Z_to_bv 64 z -> PropExec.getr R r = edenot (Eseed bvmap_empty (wenv_vals w ++ [])) (ELit z).
Proof. intros w R r z Hr. rewrite Hr. reflexivity. Qed.

Section U3I.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV ds_repA.
  Hypothesis HPDIAGE : pdiagE_stmtA H LINV ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV ds_repA.
  Hypothesis HTL : tabl_leavesA.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.

  Lemma HHi : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma popndA_set_type : forall (w : pmwA H) m m' off t (t' : Z),
    popndA H w m off t -> ffkeepX w [(948, 4)] m m' -> rw_cells asegs m' (wa_ff w + 948) [C4 (Z_to_bv 64 t')] ->
    popndA H w m' off t'.
  Proof.
    intros w m m' off t t' (P0 & P1 & P2 & P3 & P4 & P5) K C.
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact P0 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact P1 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [exact C|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact P3 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact P4 | lia | cbn; lia | vm_compute; reflexivity]|].
    eapply (ffkeepX_cell w _ m m'); [exact K | exact P5 | lia | cbn; lia | vm_compute; reflexivity].
  Qed.

  Lemma ifrA_set_ext : forall (w : pmwA H) m m' (ext' : Z),
    ifrA H w m -> ffkeepX w [(10428, 4)] m m' -> rw_cells asegs m' (wa_ff w + 10428) [C4 (Z_to_bv 64 ext')] -> 0 <= ext' < 2 ^ 31 ->
    ifrA H w m'.
  Proof.
    intros w m m' ext' (ext & tid & rid & D1 & D2 & D3 & D4 & D5 & D6 & D7 & R1 & R2 & R3) K C HX.
    exists ext', tid, rid.
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D1 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D2 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [exact C|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D4 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D5 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D6 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D7 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [exact HX|]. split; [exact R2 | exact R3].
  Qed.

  Theorem arm_ID_A : forall t, (t = 1 \/ t = 42) -> arm_stmtA H LINV t 0xefb74.
  Proof.
    intros t Ht w s LB LBs m mo c msF R F fc I tbl wv Q OK HAE IT TC TK TN PK CK AACC.
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q23 & Q24 & Q26 & Q27 & PO & C1108).
    destruct OB as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz BUD IP IC FR Hic Hend Hw MAC V3R].
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (pmxa_restrict H HHi LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X0 IT (incl_refl _)) as X0r.
    pose proof (ipure_ranges I IP) as [IWC IOP].
    destruct (Z.eq_dec wv 0) as [W0|Wn0].
    {
      assert (Q27z : PropExec.getr R 27%bv = Z_to_bv 64 0) by (rewrite Q27, W0; reflexivity).
      exact (pm_u3_id0 H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAGE w s LB LBs m mo c msF R F fc Q
               OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 BUD Q27z CK). }

    assert (HWV : 0 < wv < 2 ^ 32) by lia.

    assert (PUSH : forall mX msFX moX RX,
              PMXA H LINV w s LB LBs mX moX c S_OPER TBL_EEF44 [] -> as_AKREL H s (mkCfg msFX moX) ->
              as_VIS H s msFX = MS RX F (Z_to_bv 64 OL_PUSHK) fc None mX (seg_rom asegs) -> rfull RX ->
              regs_tbl w RX RT_PUSHK -> PropExec.getr RX 3%bv = wa_gp w -> PropExec.getr RX 4%bv = wa_tp w ->
              (forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr RX rr = PropExec.getr R rr) ->
              ictxA H w mX I -> ifrA H w mX -> popndA H w mX (c_widx c - i_io I) 1 ->
              as_SR H Q (mkCfg msFX moX)).
    { intros mX msFX moX RX XX KRX VISX RFX HTX G3X G4X KXX ICX FRX POX.
      pose proof POX as POX'. destruct POX' as (K944 & K946 & K948 & K952 & K956 & K960).
      eapply (PK s LB LBs mX moX c msFX RX F fc TBL_EEF44 1 []).
      + constructor; try assumption.
      + apply incl_refl.
      + rewrite (KXX 23%bv) by inlist. exact Q23.
      + rewrite (KXX 24%bv) by inlist. exact Q24.
      + rewrite (KXX 26%bv) by inlist. exact Q26.
      + exact K946.
      + left; lia.
      + exists (c_widx c - i_io I), 1. split; [exact K944 | exact K948].
      + exact (popnd_mdef H w mX _ _ _ _ _ _ OK K944 K946 K948 K952 K956 K960).
      + reflexivity. + reflexivity. + reflexivity.
      + change (Z.min 1 1) with 1. lia.
      + rewrite app_nil_r. reflexivity.
      + exact PmZw.seed_free_nil.
      + rewrite PmZw.Zlen_nil. lia.
      + left; reflexivity.
      + reflexivity.
      + left; reflexivity.
      + left; reflexivity.
      + intros []. }

    eapply (pm_u3i_1 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc wv Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Q27 HWV).
    intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 Gra1 G2_1 G10_1 CD1 FK1 KX1.
    pose proof (popndA_set_type w m m1 _ _ 1 PO FK1 CD1) as PO1.
    assert (IC1 : ictxA H w m1 I) by (eapply (ictxA_ffkeepX H w m m1); [exact IC | exact FK1 | vm_compute; reflexivity]).
    assert (FR1 : ifrA H w m1) by (eapply (ifrA_ffkeepX H w m m1); [exact FR | exact FK1 | vm_compute; reflexivity]).

    eapply (pm_leaf0 H HHi LINV LINV_frame AT_IS_EXT_INST 0 _ _ _ (tla_is_ext_inst HTL) (i_op I) w s LB LBs m1 mo1 c _ _ _ [] 0
              msF1 R1 F fc 0xefb8c Q OK X1 KR1 VIS1 RF1 G2_1 Gra1 eq_refl ltac:(lia) ltac:(lia) eq_refl);
      [cbn beta iota; split; [lia | rewrite G10_1; exact Q23] | vm_compute; reflexivity | reflexivity |].
    intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KEEP2 MU2 WM2 (b & Gb & _).
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(inlist)); exact G3_1).
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(inlist)); exact G4_1).
    pose proof (regs_keep w [] R1 R2 RT_ARM HT1 KEEP2) as HT2. change (rt_keep RT_ARM) with RT_ARM in HT2.
    assert (FK2 : ffkeepX w [] m1 m2).
    { apply (ffkeepX_munch w _ _ _ _ MU2 WM2). apply Forall_cons; [left; cbn [fst]; lia | apply Forall_nil]. }
    assert (KX2 : forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr R2 rr = PropExec.getr R rr).
    { intros rr Hrr. rewrite (KEEP2 rr ltac:(cbn in Hrr; decompose [or] Hrr; try contradiction; subst rr; inlist)). exact (KX1 rr Hrr). }
    destruct (popndA_ffkeepX H w m1 m2 _ _ _ OK PO1 FK2 ltac:(vm_compute; reflexivity)) as [PO2 _].
    assert (IC2 : ictxA H w m2 I) by (eapply (ictxA_ffkeepX H w m1 m2); [exact IC1 | exact FK2 | vm_compute; reflexivity]).
    assert (FR2 : ifrA H w m2) by (eapply (ifrA_ffkeepX H w m1 m2); [exact FR1 | exact FK2 | vm_compute; reflexivity]).
    destruct b.
    2: {
      assert (HTn : regs_tbl w R2 RT_I2N).
      { apply (regs_tbl_sub w [] R2 _ RT_I2N (regs_tbl_cons w [] R2 RT_ARM 10%bv (ELit 0) (regs_tbl_litI w R2 _ _ Gb) HT2)). vm_compute; reflexivity. }
      eapply (pm_u3i_n H HHbp LINV LINV_frame w s LB LBs m2 mo2 c msF2 R2 F fc Q OK X2 Htr Hbsz KR2 VIS2 RF2 FZ0 HTn G3_2 G4_2).
      intros msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 KX3 EM3. subst m3.
      apply (PUSH m2 msF3 mo3 R3 X3 KR3 VIS3 RF3 HT3 G3_3 G4_3); [| exact IC2 | exact FR2 | exact PO2].
      intros rr Hrr. rewrite (KX3 rr Hrr). exact (KX2 rr Hrr). }

    assert (HTy : regs_tbl w R2 RT_I2Y).
    { apply (regs_tbl_sub w [] R2 _ RT_I2Y (regs_tbl_cons w [] R2 RT_ARM 10%bv (ELit 1) (regs_tbl_litI w R2 _ _ Gb) HT2)). vm_compute; reflexivity. }
    pose proof PO2 as PO2'. destruct PO2' as (K944_2 & _).
    destruct (Z.eq_dec (c_widx c - i_io I) 3) as [Ho3 | Hon3].
    2: {
      eapply (pm_u3i_o H HHbp LINV LINV_frame w s LB LBs m2 mo2 c msF2 R2 F fc (c_widx c - i_io I) Q OK X2 Htr Hbsz KR2 VIS2 RF2 FZ0 HTy G3_2 G4_2
                K944_2 ltac:(lia) Hon3).
      intros msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 KX3 EM3. subst m3.
      apply (PUSH m2 msF3 mo3 R3 X3 KR3 VIS3 RF3 HT3 G3_3 G4_3); [| exact IC2 | exact FR2 | exact PO2].
      intros rr Hrr. rewrite (KX3 rr Hrr). exact (KX2 rr Hrr). }

    rewrite Ho3 in K944_2.
    eapply (pm_u3i_f H HHbp LINV LINV_frame w s LB LBs m2 mo2 c msF2 R2 F fc Q OK X2 Htr Hbsz KR2 VIS2 RF2 FZ0 HTy G3_2 G4_2 K944_2).
    intros msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 Gra3 G2_3 G10_3 G11_3 KX3 EM3. subst m3.
    destruct (rf_cell4_junk H LINV w _ _ _ _ _ _ _ _ _ _ _ 1108 X2 OK ltac:(lia) ltac:(unfold PM_RF_TOP; lia)) as (xj & Hxj & Cj).
    destruct (pm_key_rf H LINV w _ _ _ _ _ _ _ _ _ _ _ 1108 OK X2 ltac:(lia) ltac:(unfold PM_RF_TOP; lia)) as (KA1 & KA2 & KA3 & KA4).
    assert (S16 : wa_s1 w mod 16 = 0) by (clear - Q12; Z.div_mod_to_equations; lia).
    eapply (pm_find_m3 H HHbp LINV LINV_cl LINV_relro w s LB LBs m2 mo3 c _ TBL_EEF44 [] [] 0 msF3 R3 F fc 0xefbb4 (wa_s1 w + 1108) xj Q
              OK X3 ltac:(vm_compute; reflexivity) ltac:(reflexivity) KR3 VIS3 RF3 G2_3 Gra3 eq_refl ltac:(lia) G10_3 G11_3
              Cj Hxj KA1 ltac:(clear - S16; Z.div_mod_to_equations; lia) KA2 KA3 KA4).
    intros msF4 mo4 m4 R4 p KR4 VIS4 RF4 X4 KEEP4 G10_4 Hfound MU4 WM4 FFK4.
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (rewrite (KEEP4 3%bv ltac:(inlist)); exact G3_3).
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (rewrite (KEEP4 4%bv ltac:(inlist)); exact G4_3).
    pose proof (regs_keep w [] R3 R4 RT_ARM HT3 KEEP4) as HT4. change (rt_keep RT_ARM) with RT_ARM in HT4.
    pose proof (ffkeepX_nil w m2 m4 FFK4) as FK4.
    assert (KX4 : forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr R4 rr = PropExec.getr R rr).
    { intros rr Hrr. rewrite (KEEP4 rr ltac:(cbn in Hrr; decompose [or] Hrr; try contradiction; subst rr; inlist)). rewrite (KX3 rr Hrr). exact (KX2 rr Hrr). }
    destruct (popndA_ffkeepX H w m2 m4 _ _ _ OK PO2 FK4 ltac:(vm_compute; reflexivity)) as [PO4 _].
    assert (IC4 : ictxA H w m4 I) by (eapply (ictxA_ffkeepX H w m2 m4); [exact IC2 | exact FK4 | vm_compute; reflexivity]).
    assert (FR4 : ifrA H w m4) by (eapply (ifrA_ffkeepX H w m2 m4); [exact FR2 | exact FK4 | vm_compute; reflexivity]).
    destruct Hfound as [P0 | (Pp & Pce & P16 & AD4 & v & Hin & Hv & Cv)].
    {
      subst p.
      assert (HTnf : regs_tbl w R4 RT_I4NF).
      { apply (regs_tbl_sub w [] R4 _ RT_I4NF (regs_tbl_cons w [] R4 RT_ARM 10%bv (ELit 0) (regs_tbl_litI w R4 _ _ G10_4) HT4)). vm_compute; reflexivity. }
      exact (pm_u3_idnf H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAGE HU32 w s LB LBs m4 mo4 c msF4 R4 F fc Q
               OK X4 Htr Hbsz KR4 VIS4 RF4 FZ0 HTnf G3_4 G4_4 BUD CK). }

    pose proof MAC as MAC'. destruct MAC' as (_ & _ & _ & M3OK).
    assert (Hv31 : 0 <= v < 2 ^ 31) by exact (proj1 (Forall_forall _ _) M3OK (p, (xj, v)) Hin).
    eapply (pm_u3i_fd H HHbp LINV LINV_frame w s LB LBs m4 mo4 c msF4 R4 F fc p v Q OK X4 Htr Hbsz KR4 VIS4 RF4 FZ0 HT4 G3_4 G4_4
              G10_4 ltac:(clear - Pp Pce P16 AC1 AC2 AC3 AC4; split; [Z.div_mod_to_equations; nia | unfold AAPP_HI in *; lia]) AD4 Cv Hv31).
    intros msF5 mo5 m5 R5 KR5 VIS5 RF5 X5 HT5 G3_5 G4_5 KX5 CD5 FK5.
    apply (PUSH m5 msF5 mo5 R5 X5 KR5 VIS5 RF5 HT5 G3_5 G4_5).
    - intros rr Hrr. rewrite (KX5 rr Hrr). exact (KX4 rr Hrr).
    - eapply (ictxA_ffkeepX H w m4 m5); [exact IC4 | exact FK5 | vm_compute; reflexivity].
    - exact (ifrA_set_ext w m4 m5 v FR4 FK5 CD5 Hv31).
    - exact (proj1 (popndA_ffkeepX H w m4 m5 _ _ _ OK PO4 FK5 ltac:(vm_compute; reflexivity))).
  Qed.
End U3I.
