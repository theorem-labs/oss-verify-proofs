(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmHdr LbA_PmCall LbA_PmExit2 LbA_PmGlue LbA_PmU2K LbA_PmLH LbA_PmLeaf LbA_PmLeafW LbA_DiagStmt LbA_PmDS LbA_ContStmt LbA_PmVup LbA_PmWG LbA_PmWVt LbA_PmWPT LbA_PmU2 LbA_DStat LbA_TablStmt LbA_PmOL LbA_PmPD LbA_PmSL LbA_RtOwn LbA_PmU3L LbA_PmU3XK LbA_PmU3I LbA_PmWF LbA_SnStmt LbA_PmWSn LbA_PmU9K LbA_PmU9c LbA_PmU9s1_F LbA_PmU9s1_P LbA_PmU9s2 LbA_PmU9s3c LbA_PmU9d1a LbA_PmU9d1b LbA_PmU9d2 LbA_PmU9s4e LbA_PmU9s4p LbA_PmU9d3.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac inl9 := cbn; repeat (first [left; reflexivity | right]).

Section U9.
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
  Hypothesis HPDIAG0 : pdiag0_stmtA H LINV ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV ds_repA.
  Hypothesis HTL : tabl_leavesA.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.

  Hypothesis HSN : setnum_stmtA H LINV.

  Lemma HPF_C1 : In (APC0_FREE, [0xfc11c; SN_DTOR_RA1; 0xf042c]) PM_PF.
  Proof. unfold PM_PF. apply in_or_app; right. apply in_or_app; right. cbn; tauto. Qed.
  Lemma HPF_C2 : In (APC0_FREE, [0xfc11c; SN_DTOR_RA2; 0xf042c]) PM_PF.
  Proof. unfold PM_PF. apply in_or_app; right. apply in_or_app; right. cbn; tauto. Qed.
  Lemma HPF_S1 : In (APC0_FREE, [0xfc11c; SN_DTOR_RA1; 0xf19a0]) PM_PF.
  Proof. unfold PM_PF. apply in_or_app; right. apply in_or_app; right. cbn; tauto. Qed.
  Lemma HPF_S2 : In (APC0_FREE, [0xfc11c; SN_DTOR_RA2; 0xf19a0]) PM_PF.
  Proof. unfold PM_PF. apply in_or_app; right. apply in_or_app; right. cbn; tauto. Qed.

  Lemma HHe9 : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma sn_nw_range : forall bw, 0 <= sn_nw bw < 2 ^ 16.
  Proof. intros bw. unfold sn_nw. apply Z.mod_pos_bound. lia. Qed.

  Theorem arm_TYL_A : forall t, (t = 9 \/ t = 47) -> arm_stmtA H LINV t 0xefe0c.
  Proof.
    intros t Ht w s LB LBs m mo c msF R F fc I tbl wv Q OK HAE IT TC TK TN PK CK AACC.
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q23 & Q24 & Q26 & Q27 & PO & C1108).
    destruct OB as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz BUD IP IC FR Hic Hend Hw MAC V3R].
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (pmxa_restrict H HHe9 LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X0 IT (incl_refl _)) as X0r.
    pose proof (ipure_ranges I IP) as [IWC IOP].
    assert (Hio : 0 <= i_io I) by exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 IP)))))).
    assert (Hzw : zw_type t = true) by (destruct Ht as [-> | ->]; reflexivity).
    pose proof PO as (K944 & K946 & K948 & K952 & K956 & K960).

    assert (PUSHJ : forall s' LB' m' mo' msF' R' F' fc' (nk bw enc : Z),
      PMXA H LINV w s' LB' LBs m' mo' c S_OPER TBL_EEF44 [] ->
      as_AKREL H s' (mkCfg msF' mo') -> as_VIS H s' msF' = MS R' F' (Z_to_bv 64 OL_PUSHK) fc' None m' (seg_rom asegs) -> rfull R' ->
      frm_zero fc' -> regs_tbl w R' RT_PUSHK -> PropExec.getr R' 3%bv = wa_gp w -> PropExec.getr R' 4%bv = wa_tp w ->
      (forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr R' rr = PropExec.getr R rr) ->
      ffkeepX w [(946, 2); (948, 4); (952, 12)] m m' ->
      rw_cells asegs m' (wa_ff w + 946) [C2 (Z_to_bv 64 (sn_nw bw))] ->
      rw_cells asegs m' (wa_ff w + 948) [C4 (Z_to_bv 64 9)] ->
      rw_cells asegs m' (wa_ff w + 952) [C4 (Z_to_bv 64 nk)] ->
      rw_cells asegs m' (wa_ff w + 956) [C4 (Z_to_bv 64 bw)] ->
      rw_cells asegs m' (wa_ff w + 960) [C4 (Z_to_bv 64 enc)] ->
      as_SR H Q (mkCfg msF' mo')).
    { intros s' LB' m' mo' msF' R' F' fc' nk bw enc X' KR' VIS' RF' FZ' HT' G3' G4' KX' FK' C946' C948' C952' C956' C960'.
      assert (K944' : rw_cells asegs m' (wa_ff w + 944) [C2 (Z_to_bv 64 (c_widx c - i_io I))]).
      { eapply (ffkeepX_cell w _ m m'); [exact FK' | exact K944 | lia | cbn; lia | vm_compute; reflexivity]. }
      pose proof (sn_nw_range bw) as Hnw.
      eapply (PK s' LB' LBs m' mo' c msF' R' F' fc' TBL_EEF44 (sn_nw bw) []).
      + constructor; try assumption;
          first [ eapply (ictxA_ffkeepX H w m m'); [exact IC | exact FK' | vm_compute; reflexivity]
                | eapply (ifrA_ffkeepX H w m m'); [exact FR | exact FK' | vm_compute; reflexivity] ].
      + apply incl_refl.
      + rewrite (KX' 23%bv ltac:(inl9)). exact Q23.
      + rewrite (KX' 24%bv ltac:(inl9)). exact Q24.
      + rewrite (KX' 26%bv ltac:(inl9)). exact Q26.
      + exact C946'.
      + destruct (Z.eq_dec (sn_nw bw) 0) as [E0 | NE0]; [right; split; [exact E0 | split; [exact Hzw | reflexivity]] | left; lia].
      + exists (c_widx c - i_io I), 9. split; [exact K944' | exact C948'].
      + exact (popnd_mdef H w m' _ _ _ _ _ _ OK K944' C946' C948' C952' C956' C960').
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + clear - Hnw. lia.
      + rewrite app_nil_r. reflexivity.
      + exact seed_free_nil.
      + rewrite Zlen_nil. clear; lia.
      + left; reflexivity.
      + reflexivity.
      + left; reflexivity.
      + left; reflexivity.
      + intros []. }

    assert (MDSET : forall m1, ffkeepX w [(948, 4)] m m1 -> rw_cells asegs m1 (wa_ff w + 948) [C4 (Z_to_bv 64 9)] ->
              popndA H w m1 (c_widx c - i_io I) 9 /\ mdef m1 (wa_ff w + 944) 20).
    { intros m1 FK1 C948_1. pose proof (popndA_set_type H w m m1 _ _ 9 PO FK1 C948_1) as PO1. split; [exact PO1|].
      destruct PO1 as (P0 & P1 & P2 & P3 & P4 & P5). exact (popnd_mdef H w m1 _ _ _ _ _ _ OK P0 P1 P2 P3 P4 P5). }
    pose proof FR as FR'. destruct FR' as (ext & tid & rid & _ & _ & _ & Ctid & _ & _ & _ & _ & Rtid & _).
    destruct (Z.eq_dec (i_op I) 251) as [Hop | Hop].
    2: {
      eapply (pm_u9_c1 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc (i_op I) tid Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0
                Q23 IOP Hop Ctid Rtid).
      intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 Gra1 G2_1 G8_1 G10_1 G11_1 G12_1 C948_1 FK1 KX1.
      destruct (MDSET m1 FK1 C948_1) as [PO1 MD1].
      eapply (pm_set_numeric H HHbp LINV HSN w s LB LBs m1 mo1 c _ TBL_EEF44 0 msF1 R1 F fc 0xf042c tid Q OK X1
                ltac:(vm_compute; reflexivity) KR1 VIS1 RF1 FZ0 Gra1 ltac:(reflexivity) ltac:(clear; lia) G2_1 G8_1 G4_1 G10_1 G11_1 G12_1 Rtid
                ltac:(vm_compute; reflexivity) MD1 ltac:(unfold SN_COST, PM_RESERVE; clear; lia) HPF_C1 HPF_C2).
      intros msF2 mo2 m2 R2 F2 fc2 s2 LB2 r KR2 VIS2 RF2 FZ2 X2 KEEP2 G10_2 RES FK2.
      assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(inl9)); exact G3_1).
      assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(inl9)); exact G4_1).
      pose proof (regs_keep w [] R1 R2 RT_ARM HT1 KEEP2) as HT2. change (rt_keep RT_ARM) with RT_ARM in HT2.
      assert (KX2 : forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr R2 rr = PropExec.getr R rr).
      { intros rr Hrr. rewrite (KEEP2 rr ltac:(cbn in Hrr; decompose [or] Hrr; try contradiction; subst rr; inl9)). exact (KX1 rr Hrr). }
      destruct RES as [RE | (R0 & ELB & node & nk & bw & enc & HIn & Hnk & C8' & C12' & C16' & C2' & Rnk & Rbw & Renc)].
      {
        subst r.
        exact (pm_u9_c2e H HHbp LINV LINV_frame w s2 LB2 LBs m2 mo2 c msF2 R2 F2 fc2 _ Q OK X2 Htr Hbsz KR2 VIS2 RF2 FZ2 HT2 G3_2 G4_2 G10_2 BUD CK). }
      subst r LB2.
      assert (HTf : regs_tbl w R2 RT_T9F).
      { unfold RT_T9F. apply regs_tbl_app; [exact HT2|]. apply Forall_cons; [cbn [fst snd]; rewrite G10_2; reflexivity | apply Forall_nil]. }
      eapply (pm_u9_c2f H HHbp LINV LINV_frame w s2 LB LBs m2 mo2 c msF2 R2 F2 fc2 Q OK X2 Htr Hbsz KR2 VIS2 RF2 FZ2 HTf G3_2 G4_2).
      intros msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 KX3 EM3. subst m3.
      unfold PO_OFF in C8', C12', C16', C2'.
      replace (wa_ff w + 944 + 8) with (wa_ff w + 952) in C8' by (clear; lia).
      replace (wa_ff w + 944 + 12) with (wa_ff w + 956) in C12' by (clear; lia).
      replace (wa_ff w + 944 + 16) with (wa_ff w + 960) in C16' by (clear; lia).
      replace (wa_ff w + 944 + 2) with (wa_ff w + 946) in C2' by (clear; lia).
      apply (PUSHJ s2 LB m2 mo3 msF3 R3 F2 fc2 nk bw enc X3 KR3 VIS3 RF3 FZ2 HT3 G3_3 G4_3).
      - intros rr Hrr. rewrite (KX3 rr Hrr). exact (KX2 rr Hrr).
      - apply (ffkeepX_trans w [(948, 4)] [(946, 2); (952, 12)] _ m m1 m2 FK1 FK2);
          [intros x Hx; clear - Hx; cbn in Hx |- *; tauto | intros x Hx; clear - Hx; cbn in Hx |- *; tauto].
      - exact C2'.
      - eapply (ffkeepX_cell w _ m1 m2); [exact FK2 | exact C948_1 | clear; lia | cbn; clear; lia | vm_compute; reflexivity].
      - exact C8'.
      - exact C12'.
      - exact C16'. }

    assert (Q23' : PropExec.getr R 23%bv = Z_to_bv 64 251) by (rewrite Q23, Hop; reflexivity).
    assert (GR : 4 * (i_io I + 1) + 4 <= 8 * ((4 * wa_n w) / 8) \/ (4 * (i_io I + 1) = 8 * ((4 * wa_n w) / 8) /\ (4 * wa_n w) mod 8 = 4)).
    { clear - Hw1 Hio. Z.div_mod_to_equations. lia. }
    assert (Hen : 0 <= c_endian c < 2 ^ 32) by (clear - Hend; destruct Hend as [_ [E | E]]; rewrite E; lia).
    assert (AFTER1 : forall msF1 mo1 m1 R1 (x0 : Z),
      as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_FIXWORD) fc None m1 (seg_rom asegs) -> rfull R1 ->
      PMXA H LINV w s LB LBs m1 mo1 c [18; 61; 62; 63; 65; 67; 86]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ARM ->
      PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
      PropExec.getr R1 1%bv = Z_to_bv 64 0xefe78 -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) ->
      0 <= x0 < 2 ^ 32 -> PropExec.getr R1 10%bv = Z_to_bv 64 (sx32A x0) -> PropExec.getr R1 11%bv = Z_to_bv 64 (c_endian c) ->
      rw_cells asegs m1 (wa_ff w + 948) [C4 (Z_to_bv 64 9)] -> ffkeepX w [(948, 4)] m m1 ->
      (forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) ->
      as_SR H Q (mkCfg msF1 mo1)).
    2: { destruct GR as [GF | GP].
         - exact (pm_u9_s1_F H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc (i_io I) Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0
                    Q23' Q24 Hio ltac:(clear - Hw1; lia) (proj1 Hw) (proj2 Hend) GF AFTER1).
         - exact (pm_u9_s1_P H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc (i_io I) Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0
                    Q23' Q24 Hio ltac:(clear - Hw1; lia) (proj1 Hw) (proj2 Hend) GP AFTER1). }
    intros msF1 mo1 m1 R1 x0 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 Gra1 G2_1 Hx0 G10_1 G11_1 C948_1 FK1 KX1.
    destruct (MDSET m1 FK1 C948_1) as [PO1 MD1].

    eapply (pm_leafW H HHe9 LINV LINV_frame AT_FIXWORD 0 _ _ _ (tla_fixword HTL) (x0, c_endian c) [] w s LB LBs m1 mo1 c _ TBL_EEF44 [] [] 0
              msF1 R1 F fc 0xefe78 Q []);
      [ exact OK | exact X1 | exact KR1 | exact VIS1 | exact RF1 | exact G2_1 | exact Gra1 | reflexivity | clear; lia | clear; lia | reflexivity | reflexivity
      | cbn beta iota; split; [exact Hx0|]; split; [exact G10_1|]; split; [exact Hen | exact G11_1]
      | vm_compute; reflexivity | apply incl_refl | reflexivity | reflexivity
      | intros r0 r1 m9 k9 n9 a9 _ Hin9; destruct Hin9
      | ].
    intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KEEP2 MU2 WM2 (sel & Hsel & Esel).
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(inl9)); exact G3_1).
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(inl9)); exact G4_1).
    pose proof (regs_keep w [] R1 R2 RT_ARM HT1 KEEP2) as HT2. change (rt_keep RT_ARM) with RT_ARM in HT2.
    assert (FK2 : ffkeepX w [] m1 m2).
    { apply (ffkeepX_munch w _ _ _ _ MU2 WM2). apply Forall_cons; [left; cbn [fst]; clear - Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13; lia | apply Forall_nil]. }
    assert (KX2 : forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr R2 rr = PropExec.getr R rr).
    { intros rr Hrr. rewrite (KEEP2 rr ltac:(cbn in Hrr; decompose [or] Hrr; try contradiction; subst rr; inl9)). exact (KX1 rr Hrr). }

    eapply (pm_u9_s2 H HHbp LINV LINV_frame w s LB LBs m2 mo2 c msF2 R2 F fc sel Q OK X2 Htr Hbsz KR2 VIS2 RF2 FZ0 HT2 G3_2 G4_2 Esel Hsel).
    intros msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 Gra3 G2_3 G10_3 G11_3 CK3 FK3 KX3.
    destruct (pm_key_rf H LINV w _ _ _ _ _ _ _ _ _ _ _ 1104 OK X3 ltac:(clear; lia) ltac:(unfold PM_RF_TOP; clear; lia)) as (KA1 & KA2 & KA3 & KA4).
    assert (S16 : wa_s1 w mod 16 = 0) by (clear - Q12; Z.div_mod_to_equations; lia).
    eapply (pm_find_m1 H HHbp LINV LINV_cl LINV_relro w s LB LBs m3 mo3 c _ TBL_EEF44 [] [] 0 msF3 R3 F fc 0xefe88 (wa_s1 w + 1104) sel Q
              OK X3 ltac:(vm_compute; reflexivity) ltac:(reflexivity) KR3 VIS3 RF3 G2_3 Gra3 eq_refl ltac:(clear; lia) G10_3 G11_3
              CK3 Hsel KA1 ltac:(clear - S16; Z.div_mod_to_equations; lia) KA2 KA3 KA4).
    intros msF4 mo4 m4 R4 p KR4 VIS4 RF4 X4 KEEP4 G10_4 Hfound MU4 WM4 FFK4.
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (rewrite (KEEP4 3%bv ltac:(inl9)); exact G3_3).
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (rewrite (KEEP4 4%bv ltac:(inl9)); exact G4_3).
    pose proof (regs_keep w [] R3 R4 RT_ARM HT3 KEEP4) as HT4. change (rt_keep RT_ARM) with RT_ARM in HT4.
    pose proof (ffkeepX_nil w m3 m4 FFK4) as FK4.
    assert (KX4 : forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr R4 rr = PropExec.getr R rr).
    { intros rr Hrr. rewrite (KEEP4 rr ltac:(cbn in Hrr; decompose [or] Hrr; try contradiction; subst rr; inl9)). rewrite (KX3 rr Hrr). exact (KX2 rr Hrr). }
    assert (CK4 : rw_cells asegs m4 (wa_s1 w + 1104) [C4 (Z_to_bv 64 sel)]).
    { eapply rw_cells_transport; [exact CK3 | exact MU4 | exact WM4 |].
      cbn [disjoint_from cells_size csize]. split; [right; clear; lia | exact Logic.I]. }
    assert (FK14 : ffkeepX w [] m1 m4).
    { apply (ffkeepX_trans w [] [] _ m1 m2 m4 FK2); [| apply incl_refl | apply incl_refl].
      exact (ffkeepX_trans w _ _ _ m2 m3 m4 FK3 FK4 (incl_refl _) (incl_refl _)). }
    destruct Hfound as [P0 | (Pp & Pce & P16 & AD4 & v & Hin & Hv & Cv)].
    {
      subst p.
      assert (HTnf : regs_tbl w R4 RT_T9F).
      { unfold RT_T9F. apply regs_tbl_app; [exact HT4|]. apply Forall_cons; [cbn [fst snd]; rewrite G10_4; reflexivity | apply Forall_nil]. }
      exact (pm_u9_d1a H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HU32 HPDIAG0 w s LB LBs m4 mo4 c msF4 R4 F fc Q
               OK X4 Htr Hbsz KR4 VIS4 RF4 FZ0 HTnf G3_4 G4_4 BUD CK). }
    assert (Pbnd : 0 < p /\ p + 24 <= 2 ^ 47) by (clear - Pp Pce AC1 AC2 AC3 AC4; unfold AAPP_HI in *; lia).
    pose proof (proj2 Cv) as Fv.
    destruct (Z.eq_dec v 0) as [V0 | VN].
    {
      subst v.
      exact (pm_u9_d1b H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HU32 HPDIAG0 w s LB LBs m4 mo4 c msF4 R4 F fc p Q
               OK X4 Htr Hbsz KR4 VIS4 RF4 FZ0 HT4 G3_4 G4_4 G10_4 Pbnd AD4 Fv BUD CK). }
    assert (Hv' : 0 < v < 2 ^ 32) by (clear - Hv VN; lia).
    destruct (Z.eq_dec sel v) as [SV | SNV].
    {
      subst sel.
      exact (pm_u9_d2 H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HU32 HPDIAG0 w s LB LBs m4 mo4 c msF4 R4 F fc p v Q
               OK X4 Htr Hbsz KR4 VIS4 RF4 FZ0 HT4 G3_4 G4_4 G10_4 Pbnd AD4 Fv Hv' CK4 BUD CK). }

    eapply (pm_u9_s3c H HHbp LINV LINV_frame w s LB LBs m4 mo4 c msF4 R4 F fc p v sel Q OK X4 Htr Hbsz KR4 VIS4 RF4 FZ0 HT4 G3_4 G4_4
              G10_4 Pbnd AD4 Fv Hv' CK4 Hsel SNV).
    intros msF5 mo5 m5 R5 KR5 VIS5 RF5 X5 HT5 G3_5 G4_5 Gra5 G2_5 G8_5 G10_5 G11_5 G12_5 EM5 KX5. subst m5.
    destruct (popndA_ffkeepX H w m1 m4 _ _ _ OK PO1 FK14 ltac:(vm_compute; reflexivity)) as [PO4 MD4].
    eapply (pm_set_numeric H HHbp LINV HSN w s LB LBs m4 mo5 c _ TBL_EEF44 0 msF5 R5 F fc 0xf19a0 v Q OK X5
              ltac:(vm_compute; reflexivity) KR5 VIS5 RF5 FZ0 Gra5 ltac:(reflexivity) ltac:(clear; lia) G2_5 G8_5 G4_5 G10_5 G11_5 G12_5 Hv
              ltac:(vm_compute; reflexivity) MD4 ltac:(unfold SN_COST, PM_RESERVE; clear; lia) HPF_S1 HPF_S2).
    intros msF6 mo6 m6 R6 F6 fc6 s6 LB6 r KR6 VIS6 RF6 FZ6 X6 KEEP6 G10_6 RES FK6.
    assert (G3_6 : PropExec.getr R6 3%bv = wa_gp w) by (rewrite (KEEP6 3%bv ltac:(inl9)); exact G3_5).
    assert (G4_6 : PropExec.getr R6 4%bv = wa_tp w) by (rewrite (KEEP6 4%bv ltac:(inl9)); exact G4_5).
    pose proof (regs_keep w [] R5 R6 RT_ARM HT5 KEEP6) as HT6. change (rt_keep RT_ARM) with RT_ARM in HT6.
    assert (KX6 : forall rr : reg, In rr [23%bv; 24%bv; 26%bv] -> PropExec.getr R6 rr = PropExec.getr R rr).
    { intros rr Hrr. rewrite (KEEP6 rr ltac:(cbn in Hrr; decompose [or] Hrr; try contradiction; subst rr; inl9)). rewrite (KX5 rr Hrr). exact (KX4 rr Hrr). }
    destruct RES as [RE | (R0 & ELB & node & nk & bw & enc & HIn & Hnk & C8' & C12' & C16' & C2' & Rnk & Rbw & Renc)].
    {
      subst r.
      exact (pm_u9_s4e H HHbp LINV LINV_frame w s6 LB6 LBs m6 mo6 c msF6 R6 F6 fc6 _ Q OK X6 Htr Hbsz KR6 VIS6 RF6 FZ6 HT6 G3_6 G4_6 G10_6 BUD CK). }
    subst r LB6.
    assert (HTf : regs_tbl w R6 RT_T9F).
    { unfold RT_T9F. apply regs_tbl_app; [exact HT6|]. apply Forall_cons; [cbn [fst snd]; rewrite G10_6; reflexivity | apply Forall_nil]. }
    unfold PO_OFF in C8', C12', C16', C2'.
    replace (wa_ff w + 944 + 8) with (wa_ff w + 952) in C8' by (clear; lia).
    replace (wa_ff w + 944 + 12) with (wa_ff w + 956) in C12' by (clear; lia).
    replace (wa_ff w + 944 + 16) with (wa_ff w + 960) in C16' by (clear; lia).
    replace (wa_ff w + 944 + 2) with (wa_ff w + 946) in C2' by (clear; lia).
    destruct (Z.eq_dec nk 1) as [N1 | NN1]; [| destruct (Z.eq_dec nk 2) as [N2 | NN2]].
    3: {
      exact (pm_u9_d3 H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HU32 HPDIAG0 w s6 LB LBs m6 mo6 c msF6 R6 F6 fc6 nk Q
               OK X6 Htr Hbsz KR6 VIS6 RF6 FZ6 HTf G3_6 G4_6 C8' Rnk (conj NN1 NN2) BUD CK). }
    all: eapply (pm_u9_s4p H HHbp LINV LINV_frame w s6 LB LBs m6 mo6 c msF6 R6 F6 fc6 nk Q OK X6 Htr Hbsz KR6 VIS6 RF6 FZ6 HTf G3_6 G4_6
                   C8' Rnk ltac:(clear - N1 || clear - N2; lia)).
    all: intros msF7 mo7 m7 R7 KR7 VIS7 RF7 X7 HT7 G3_7 G4_7 KX7 EM7; subst m7.
    all: apply (PUSHJ s6 LB m6 mo7 msF7 R7 F6 fc6 nk bw enc X7 KR7 VIS7 RF7 FZ6 HT7 G3_7 G4_7);
      [ intros rr Hrr; rewrite (KX7 rr Hrr); exact (KX6 rr Hrr)
      | apply (ffkeepX_trans w [(948, 4)] [(946, 2); (952, 12)] _ m m4 m6);
          [ apply (ffkeepX_trans w [(948, 4)] [] _ m m1 m4 FK1 FK14); [apply incl_refl | apply incl_nil_l]
          | exact FK6
          | intros x Hx; clear - Hx; cbn in Hx |- *; tauto
          | intros x Hx; clear - Hx; cbn in Hx |- *; tauto ]
      | exact C2'
      | eapply (ffkeepX_cell w _ m4 m6); [exact FK6 | exact (proj1 (proj2 (proj2 PO4))) | clear; lia | cbn; clear; lia | vm_compute; reflexivity]
      | exact C8'
      | exact C12'
      | exact C16' ].
  Qed.
End U9.
