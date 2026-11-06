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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmHdr LbA_PmCall LbA_PmXp LbA_PmExit LbA_PmInit LbA_PmFin LbA_PmExit2 LbA_DiagStmt LbA_PmDS LbA_PmGlue.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_PmHdr2 LbA_PmHex LbA_PmBMT LbA_PmBMC1 LbA_PmBMC2 LbA_PmMM LbA_PmIH.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma rdn1_of_mdef : forall m a, mdef m a 1 -> 0 <= a -> a + 1 < 2 ^ 64 ->
  exists b, PropExec.rdn asegs m (Z_to_bv 64 a) 1 = Some [b].
Proof.
  intros m a MD H0 H1. pose proof (MD 0 ltac:(lia)) as D. rewrite Z.add_0_r in D.
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [| contradiction].
  exists b. cbn [PropExec.rdn]. rewrite E. reflexivity.
Qed.

Section Mag.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.
  Hypothesis HCTOR : ds_ctor_stmtA H LINV ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV ds_repA.
  Hypothesis HU64 : put_u64_stmtA H LINV ds_repA.

  Lemma HHmg : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma pm_hdr_a2 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [] TBL_ED284 [] ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xed414) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_ED284 ->
    wa_words w <> 0 -> 4 < wa_n w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xeda9c) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXA H LINV w s LB LBs m1 mo1 c [OB_BINARY] TBL_ED90C [] -> regs_tbl w R1 RT_ED90C ->
       PropExec.getr R1 3%bv = PropExec.getr R 3%bv -> PropExec.getr R1 4%bv = PropExec.getr R 4%bv ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q OK X KR VIS RF HT HW HN K.
    pm_go HHmg LINV_frame OK X KR VIS RF HT (@nil word) (@nil kentry) 400%nat [0xeda9c] [false; true] 41%N
          [OB_BINARY] [968; 1040; 1048] (@nil Z) TBL_ED90C (@nil (Z * expr)) RT_ED90C.
    - pose proof (wk_n H w OK) as N1. pose proof (wk_words H w OK) as W1.
      assert (Hw : 0 <= wa_words w < 2 ^ 64).
      { destruct W1 as [[E0 _]|(pw & k & _ & Rg & W0 & _ & Whi & _ & _)]; lia. }
      split_scs; pm_br H w (Eseed R (wenv_vals w ++ [])) (env_world_seed H w R []).
    - intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HT1 HR1 _.
      eapply K; [exact KR1 | exact VIS1 | exact RF1 | exact X1 | exact HT1 | rewrite (HR1 3%bv); reflexivity | rewrite (HR1 4%bv); reflexivity].
  Qed.

  Lemma pm_magic : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (p : Z) (c0 : parserC) (ff fp : Z)
      (LB0 : list block) (LF : list fframe) (CH : list (Z * Z)) (m0 : mem) (mo0 : Model) (st0 : as_St H) (lo B shi : Z)
      s LB LBs m mo c msF R F fc,
    let w := pm_world H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi in
    let Q := pm_post H LINV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st0 LB0 LF p c0 lo B shi m0 mo0 in
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [86]%nat TBL_ED90C [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xeda9c) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ED90C -> PropExec.getr R 3%bv = gp -> PropExec.getr R 4%bv = tp ->
    wa_words w <> 0 -> 4 < wa_n w ->
    hdr_good_K H LINV w s LB LBs c F fc Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c msF R F fc
           w Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3 G4 HW0 HN4 K.
    pose proof (xa_wbuf _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0 HW0) as WB.
    pose proof (pmw_bounds H w OK) as BND.
    assert (WR : 0 <= wa_words w /\ wa_words w + 4 * wa_n w <= 2 ^ 47).
    { pose proof (wk_words H w OK) as W1.
      destruct W1 as [[E0 _]|(pw & k & _ & Rg & W0 & _ & Whi & _ & _)]; [contradiction | lia]. }
    destruct (rdn1_of_mdef m (wa_words w + 0) ltac:(intros i Hi; replace (wa_words w + 0 + i) with (wa_words w + i) by lia; apply WB; lia) ltac:(lia) ltac:(lia)) as (b0 & RB0).
    destruct (rdn1_of_mdef m (wa_words w + 1) ltac:(intros i Hi; replace (wa_words w + 1 + i) with (wa_words w + (1 + i)) by lia; apply WB; lia) ltac:(lia) ltac:(lia)) as (b1 & RB1).
    destruct (rdn1_of_mdef m (wa_words w + 2) ltac:(intros i Hi; replace (wa_words w + 2 + i) with (wa_words w + (2 + i)) by lia; apply WB; lia) ltac:(lia) ltac:(lia)) as (b2 & RB2).
    destruct (rdn1_of_mdef m (wa_words w + 3) ltac:(intros i Hi; replace (wa_words w + 3 + i) with (wa_words w + (3 + i)) by lia; apply WB; lia) ltac:(lia) ltac:(lia)) as (b3 & RB3).
    destruct (Z.eq_dec (bv_unsigned b0) 3) as [E0|E0].
    - destruct (Z.eq_dec (bv_unsigned b1) 2) as [E1|E1].
      + destruct (Z.eq_dec (bv_unsigned b2) 35) as [E2|E2].
        * destruct (Z.eq_dec (bv_unsigned b3) 7) as [E3|E3].
          -- exact (pm_hdr_b_le H HHmg LINV LINV_frame w s LB LBs m mo c msF R F fc Q b0 b1 b2 b3 OK X0 KR0 VIS0 RF0 HT0 G3 G4 HW0 HN4
                      RB0 RB1 RB2 RB3 E0 E1 E2 E3 K).
          -- exact (pm_bm_30 H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR HU32 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                      p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c msF R F fc b0 b1 b2 b3
                      OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3 G4 HW0 HN4 RB0 RB1 RB2 RB3 E0 E1 E2 E3).
        * exact (pm_bm_20 H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR HU32 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c msF R F fc b0 b1 b2 b3
                    OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3 G4 HW0 HN4 RB0 RB1 RB2 RB3 E0 E1 E2).
      + exact (pm_bm_10 H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR HU32 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c msF R F fc b0 b1 b2 b3
                  OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3 G4 HW0 HN4 RB0 RB1 RB2 RB3 E0 E1).
    - destruct (Z.eq_dec (bv_unsigned b0) 7) as [F0|F0].
      + destruct (Z.eq_dec (bv_unsigned b1) 35) as [F1|F1].
        * destruct (Z.eq_dec (bv_unsigned b2) 2) as [F2|F2].
          -- destruct (Z.eq_dec (bv_unsigned b3) 3) as [F3|F3].
             ++ exact (pm_hdr_b_be H HHmg LINV LINV_frame w s LB LBs m mo c msF R F fc Q b0 b1 b2 b3 OK X0 KR0 VIS0 RF0 HT0 G3 G4 HW0 HN4
                         RB0 RB1 RB2 RB3 F0 F1 F2 F3 K).
             ++ exact (pm_bm_03 H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR HU32 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                         p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c msF R F fc b0 b1 b2 b3
                         OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3 G4 HW0 HN4 RB0 RB1 RB2 RB3 F0 F1 F2 F3).
          -- exact (pm_bm_02 H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR HU32 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                      p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c msF R F fc b0 b1 b2 b3
                      OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3 G4 HW0 HN4 RB0 RB1 RB2 RB3 F0 F1 F2).
        * exact (pm_bm_01 H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR HU32 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c msF R F fc b0 b1 b2 b3
                    OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3 G4 HW0 HN4 RB0 RB1 RB2 RB3 F0 F1).
      + exact (pm_bm_00 H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR HU32 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c msF R F fc b0 b1 b2 b3
                  OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3 G4 HW0 HN4 RB0 RB1 RB2 RB3 E0 F0).
  Qed.

  Lemma pm_hdr : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (p : Z) (c0 : parserC) (ff fp : Z)
      (LB0 : list block) (LF : list fframe) (CH : list (Z * Z)) (m0 : mem) (mo0 : Model) (st0 : as_St H) (lo B shi : Z)
      s LB LBs m mo c msF R F fc,
    let w := pm_world H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi in
    let Q := pm_post H LINV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st0 LB0 LF p c0 lo B shi m0 mo0 in
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [] TBL_ED284 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xed414) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ED284 -> PropExec.getr R 3%bv = gp -> PropExec.getr R 4%bv = tp ->
    hdr_good_K H LINV w s LB LBs c F fc Q ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c msF R F fc
           w Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3 G4 K.
    destruct (Z.eq_dec (wa_words w) 0) as [HW0|HW0].
    - exact (pm_mm H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c msF R F fc OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3 G4 HW0).
    - destruct (Z_le_gt_dec (wa_n w) 4) as [HN4|HN4].
      + exact (pm_ih H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR HU32 HU64 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c msF R F fc OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3 G4 HW0 HN4).
      + assert (HN4' : 4 < wa_n w) by lia.
        eapply (pm_hdr_a2 w s LB LBs m mo c msF R F fc Q OK X0 KR0 VIS0 RF0 HT0 HW0 HN4').
        intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3' G4'.
        exact (pm_magic ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m1 mo1 c
                 msF1 R1 F fc OK X1 Htr Hbsz KR1 VIS1 RF1 FZ0 HT1 (eq_trans G3' G3) (eq_trans G4' G4) HW0 HN4' K).
  Qed.
End Mag.
