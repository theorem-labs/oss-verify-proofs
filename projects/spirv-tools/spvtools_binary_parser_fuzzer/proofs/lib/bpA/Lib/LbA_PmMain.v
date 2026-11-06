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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_PmHdr2 LbA_TablStmt LbA_PmLeaf LbA_PmMag LbA_PmLH LbA_PmHTail LbA_PmLExit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma init_budA : forall st e n, fresh_state st (st_words st) (st_nwords st) -> 0 <= n ->
  pm_bud n (set_scalA (set_scalA (pmc_of st) (c_widx (pmc_of st)) (c_icount (pmc_of st)) e e) 5
                      (c_icount (pmc_of st)) e e).
Proof.
  intros st e n FR Hn. destruct FR as (_ & _ & _ & _ & _ & Hm1 & Hm2 & Hm3 & _).
  unfold pm_bud, pmc_of, set_scalA. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd].
  rewrite Hm1, Hm2, Hm3. unfold t3b, t3c, Zlength, OPND_SZ. cbn [fst snd length Z.of_nat].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); try lia. intros b [].
Qed.

Section Main.
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
  Hypothesis HTL : tabl_leavesA.

  Definition pm_body_all : Prop :=
    forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (p : Z) (c0 : parserC) (ff fp : Z)
           (LB0 : list block) (LF : list fframe) (CH : list (Z * Z)) (m0 : mem) (mo0 : Model) (st0 : as_St H) (lo B shi : Z)
           (F : bvmap 5 word) (fc : bv 32),
      let w := pm_world H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi in
      pmw_okA H w ->
      body_stmtA H LINV w (pm_post H LINV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st0 LB0 LF p c0 lo B shi m0 mo0).
  Hypothesis BODY : pm_body_all.

  Theorem parse_module_okA : parse_module_stmtA H LINV.
  Proof.
    unfold parse_module_stmtA.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LB0 LBs LF CH p c
           lo B shi errv VIS FZ Ha0 PR PSH FIN CIN C16 CWR FRESH Hn WOK SOWN LBOWN RH KR MS1 MS2 MS3 RA SPB B64 SP16
           STK CE LO ERR MI TP RA2 LI AC RFS LFB S0 SPS CHN HPF CHF HTR ALC.
    eapply (pm_init H HHbp LINV LINV_frame ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc msF m mo s LB LB0 LBs LF CH p c lo B shi errv _ VIS Ha0 PR PSH FIN CIN C16 CWR FRESH Hn WOK SOWN LBOWN RH KR
              MS1 MS2 MS3 RA SPB B64 SP16 STK CE LO ERR MI TP RA2 LI AC RFS LFB S0 SPS CHN CHF HTR HPF ALC).
    intros ff fp msF1 mo1 m1 R1 w OK X1 KR1 VIS1 RF1 HT1 G3_1 G4_1.
    pose proof (fresh_blocks (pc_state c) _ _ FRESH) as (_ & CB).
    assert (Hbsz : forall q k, In (q, k) (c_blocks (pmc_of (pc_state c))) -> k <= 2 ^ 40).
    { intros q k Hin. rewrite CB in Hin. cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as _ <-; lia. }
    pose proof FRESH as FR'. destruct FR' as (_ & _ & Fw & Fic & Ffl & _).
    eapply (pm_hdr H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR HU32 HU64 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              p c ff fp LB0 LF CH m mo s lo B shi s LB LBs m1 mo1 (pmc_of (pc_state c)) msF1 R1 F fc OK X1 eq_refl Hbsz KR1 VIS1 RF1 FZ HT1 G3_1 G4_1).

    intros msF2 mo2 m2 R2 e He KR2 VIS2 RF2 X2 HT2 G3_2 G4_2 HW HN.
    eapply (pm_htail H HHbp LINV LINV_frame ds_repA DSL HCTOR HCSEQ HDTOR HTL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              p c ff fp LB0 LF CH m mo s lo B shi s LB LBs m2 mo2 _ msF2 R2 F fc OK X2 eq_refl Hbsz KR2 VIS2 RF2 FZ HT2 G3_2 G4_2 HW HN
              He ltac:(cbn [set_scalA c_icount pmc_of]; exact Fic) ltac:(cbn [set_scalA c_widx pmc_of]; rewrite Fw; lia)).

    intros msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3.
    set (c3 := set_scalA (set_scalA (pmc_of (pc_state c)) (c_widx (pmc_of (pc_state c))) (c_icount (pmc_of (pc_state c))) e e) 5
                 (c_icount (set_scalA (pmc_of (pc_state c)) (c_widx (pmc_of (pc_state c))) (c_icount (pmc_of (pc_state c))) e e))
                 (c_endian (set_scalA (pmc_of (pc_state c)) (c_widx (pmc_of (pc_state c))) (c_icount (pmc_of (pc_state c))) e e))
                 (c_reqconv (set_scalA (pmc_of (pc_state c)) (c_widx (pmc_of (pc_state c))) (c_icount (pmc_of (pc_state c))) e e))) in *.
    assert (HL : LIA H LINV w s LB LBs m3 mo3 c3 msF3 R3 F fc).
    { constructor.
      - exact X3.
      - exact KR3.
      - exact VIS3.
      - exact RF3.
      - exact FZ.
      - exact HT3.
      - exact G3_3.
      - exact G4_3.
      - reflexivity.
      - exact Hbsz.
      - subst c3. cbn [set_scalA c_icount c_widx pmc_of]. rewrite Fic. lia.
      - subst c3. cbn [set_scalA c_endian c_reqconv]. split; [reflexivity | exact He].
      - split; [exact HW | change (4 < wa_n w) in HN; lia].
      - subst c3. exact (init_budA (pc_state c) e (wa_n w) FRESH
                           ltac:(pose proof (wk_n H w OK); lia)).
      - subst c3. destruct FRESH as (_ & _ & _ & _ & _ & Hm1 & Hm2 & Hm3 & _).
        unfold nodesA, macctA, m3okA, laccA, pmc_of, set_scalA. cbn [c_m1 c_m2 c_m3 c_widx]. rewrite Hm1, Hm2, Hm3.
        unfold Zlen. cbn [t3b t3c fst snd length Z.of_nat]. repeat split; try lia. apply Forall_nil. }
    eapply (pm_loopA H LINV w _ _ _ s LB LBs m3 mo3 c3 msF3 R3 F fc HL).
    Unshelve.
    -
      intros s' LB' LBs' m' mo' c' msF' R' F' fc' HL' HEX.
      exact (pm_lexit H HHbp LINV LINV_frame ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c ff fp LB0 LF CH m mo s lo B shi
               s' LB' LBs' m' mo' c' msF' R' F' fc' OK (la_x _ _ _ _ _ _ _ _ _ _ _ _ _ HL') (la_tr _ _ _ _ _ _ _ _ _ _ _ _ _ HL')
               (la_bsz _ _ _ _ _ _ _ _ _ _ _ _ _ HL') (la_kr _ _ _ _ _ _ _ _ _ _ _ _ _ HL') (la_vis _ _ _ _ _ _ _ _ _ _ _ _ _ HL')
               (la_rf _ _ _ _ _ _ _ _ _ _ _ _ _ HL') (la_fz _ _ _ _ _ _ _ _ _ _ _ _ _ HL') (la_rt _ _ _ _ _ _ _ _ _ _ _ _ _ HL')
               (la_gp _ _ _ _ _ _ _ _ _ _ _ _ _ HL') (la_tp _ _ _ _ _ _ _ _ _ _ _ _ _ HL') HW HEX).
    -
      exact (BODY ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c ff fp LB0 LF CH m mo s lo B shi F fc OK).
  Qed.
End Main.
