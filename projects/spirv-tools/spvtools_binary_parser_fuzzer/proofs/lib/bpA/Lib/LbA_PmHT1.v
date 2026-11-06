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
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_PmHdr2 LbA_PmHex LbA_TablStmt LbA_PmLeaf.

Definition RT_EE030 : list (reg * expr) := [(1%bv, ELit 975296); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, ELit 2147450880); (19%bv, EVar 32); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 2147450880); (22%bv, EAlu ALU_ADD (EVar 32) (ELit 88)); (23%bv, EAlu ALU_ADD (EVar 33) (ELit 13584)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 14640)); (26%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880))].
Definition TBL_EE030 : list (Z * expr) := TBL_EDFD8 ++ [(632, WADD WV_P 92)].

Definition RT_PM_HT1_1 : list (reg * expr) := [(1%bv, ELit 975252); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (13%bv, EAlu ALU_ADD (EVar 32) (ELit 92)); (18%bv, ELit 2147450880); (19%bv, EVar 32); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 2147450880); (22%bv, EAlu ALU_ADD (EVar 32) (ELit 88)); (23%bv, EAlu ALU_ADD (EVar 33) (ELit 13584)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 14640)); (25%bv, EAlu ALU_ADD (EVar 33) (ELit 11488)); (26%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880))].
Definition RT_PM_HT1_3 : list (reg * expr) := [(1%bv, ELit 975296); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (12%bv, ELit 0); (18%bv, ELit 2147450880); (19%bv, EVar 32); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, ELit 2147450880); (22%bv, EAlu ALU_ADD (EVar 32) (ELit 88)); (23%bv, EAlu ALU_ADD (EVar 33) (ELit 13584)); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 14640)); (26%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880))].

Section HT1.
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
  Hypothesis HTL : tabl_leavesA.

  Lemma HHm : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

#[local] Definition HTLbAPmHT1_0 : list (Z * expr) := [(1056, EVar 33); (968, EVar 33); (1040, EVar 33); (1048, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 56)) (ELit 3)) (ELit 2147450880)); (1000, EAlu ALU_ADD (EVar 32) (ELit 48)); (1008, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880)); (936, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 88)) (ELit 3)) (ELit 2147450880)); (944, EAlu ALU_ADD (EVar 32) (ELit 56)); (960, EAlu ALU_ADD (EVar 33) (ELit 11488)); (712, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 92)) (ELit 3)) (ELit 2147450880)); (632, EAlu ALU_ADD (EVar 32) (ELit 92))].
  Lemma pm_ht1 : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (p : Z) (c0 : parserC) (ff fp : Z)
      (LB0 : list block) (LF : list fframe) (CH : list (Z * Z)) (m0 : mem) (mo0 : Model) (st0 : as_St H) (lo B shi : Z)
      s LB LBs m mo c msF R F fc (Q : config -> Prop),
    let w := pm_world H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi in
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [86]%nat TBL_EDFD8 FTBL_EDFD8 -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xee168) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_EDFD8 -> PropExec.getr R 3%bv = gp -> PropExec.getr R 4%bv = tp ->
    wa_words w <> 0 ->
    4 < wa_n w ->
    c_endian c = 0 \/ c_endian c = 1 ->
    (forall msF1 mo1 m1 R1 (r : Z), as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xee1c0) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [86]%nat TBL_EE030 FTBL_EDFD8 -> regs_tbl w R1 RT_EE030 -> PropExec.getr R1 3%bv = gp -> PropExec.getr R1 4%bv = tp -> 0 <= r < 2 ^ 32 -> PropExec.getr R1 10%bv = Z_to_bv 64 (sx32A r) -> PropExec.getr R1 27%bv = Z_to_bv 64 (c_endian c) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c msF R F fc Q
           w OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 HW0 HN4 HEN KV.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    assert (WR : 0 <= wa_words w /\ wa_words w + 4 * wa_n w <= 2 ^ 47) by (destruct (wk_words H w OK) as [[E0 _]|(pw & k0 & _ & Rg & W0 & _ & Whi & _ & _)]; [contradiction | lia]).
    destruct (rdn4_of_mdef m (wa_words w + 0) ltac:(intros i Hi; replace (wa_words w + 0 + i) with (wa_words w + (0 + i)) by lia; apply (xa_wbuf _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0 HW0); lia) ltac:(lia) ltac:(lia)) as (bs0 & RD0 & LN0).
    pose proof (bytes_le_to_Z_range4 bs0 LN0) as XR0.
    set (x0 := bytes_le_to_Z bs0) in *.
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 (c_endian c); Z_to_bv 64 (bv_swrap 32 x0)]
          [KDisj (SA (EVar WV_WORDS) 0) (ELit 20) (SA (EVar WV_S1) PM_RF_LO) (ELit (1216 - PM_RF_LO)); KDisj (SA (EVar WV_WORDS) 0) (ELit 20) (SA (EVar WV_FF) 0) (ELit 16384)] 400%nat [AT_FIXWORD] (@nil bool) 41%N
          [86]%nat [632] (@nil Z) HTLbAPmHT1_0 [(14640, EVar 36); (14648, EVar 37)] RT_PM_HT1_1.
    { pose proof (pmw_bounds H w OK) as BND. split_scs; first [ sc_w4 H w (Eseed R (wenv_vals w ++ [Z_to_bv 64 (c_endian c); Z_to_bv 64 (bv_swrap 32 x0)])) (env_world_seed H w R [Z_to_bv 64 (c_endian c); Z_to_bv 64 (bv_swrap 32 x0)]) | sc_fld4 H w (Eseed R (wenv_vals w ++ [Z_to_bv 64 (c_endian c); Z_to_bv 64 (bv_swrap 32 x0)])) (env_world_seed H w R [Z_to_bv 64 (c_endian c); Z_to_bv 64 (bv_swrap 32 x0)]) (xa_endian _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) ]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (G3_1 : PropExec.getr R1 3%bv = gp) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = tp) by (rewrite (HR1 4%bv); exact G4_0).
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_HT1_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    eapply (pm_leaf0 H HHm LINV LINV_frame AT_FIXWORD 0 _ _ _ (tla_fixword HTL) ((x0, c_endian c)) w _ _ _ _ _ c _ _ _ _ _ msF1 R1 F fc 975252 _);
      [exact OK | exact X1 | exact KR1 | exact VIS1 | exact RF1 | rtf HT1 | rtf HT1 | reflexivity | lia | lia | reflexivity
      | cbn beta iota; split; [exact XR0|]; split; [rewrite (HR1 10%bv); exact (swrap32_sx32A x0 XR0)|]; split; [lia|]; rewrite (HR1 11%bv); reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | ].
    intros msF2 mo2 M2 R2 KR2 VIS2 RF2 X2 KEEP2 MU2 WM2 (r0 & Hr0 & Er0).
    assert (G3_2 : PropExec.getr R2 3%bv = gp) by (rewrite (KEEP2 3%bv ltac:(inb)); exact G3_1).
    assert (G4_2 : PropExec.getr R2 4%bv = tp) by (rewrite (KEEP2 4%bv ltac:(inb)); exact G4_1).
    pose proof (regs_keep w [] R1 R2 RT_PM_HT1_1 HT1 KEEP2) as HT2.
    assert (E27_2 : PropExec.getr R2 27%bv = Z_to_bv 64 (c_endian c)) by (rewrite (KEEP2 27%bv ltac:(inb)); rewrite (HR1 27%bv); reflexivity).
    destruct (rdn4_of_mdef M2 (wa_words w + 4) ltac:(intros i Hi; replace (wa_words w + 4 + i) with (wa_words w + (4 + i)) by lia; apply (xa_wbuf _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 HW0); lia) ltac:(lia) ltac:(lia)) as (bs1 & RD1 & LN1).
    pose proof (bytes_le_to_Z_range4 bs1 LN1) as XR1.
    set (x1 := bytes_le_to_Z bs1) in *.
    pm_go HHm LINV_frame OK X2 KR2 VIS2 RF2 HT2 [Z_to_bv 64 (bv_swrap 32 x1)]
          [KDisj (SA (EVar WV_WORDS) 0) (ELit 20) (SA (EVar WV_S1) PM_RF_LO) (ELit (1216 - PM_RF_LO)); KDisj (SA (EVar WV_WORDS) 0) (ELit 20) (SA (EVar WV_FF) 0) (ELit 16384)] 400%nat [AT_FIXWORD] (@nil bool) 41%N
          [86]%nat (@nil Z) (@nil Z) HTLbAPmHT1_0 [(14640, EVar 36); (14648, EVar 37)] RT_PM_HT1_3.
    { pose proof (pmw_bounds H w OK) as BND. split_scs; sc_w4 H w (Eseed R2 (wenv_vals w ++ [Z_to_bv 64 (bv_swrap 32 x1)])) (env_world_seed H w R2 [Z_to_bv 64 (bv_swrap 32 x1)]). }
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
    assert (G3_3 : PropExec.getr R3 3%bv = gp) by (rewrite (HR3 3%bv); exact G3_2).
    assert (G4_3 : PropExec.getr R3 4%bv = tp) by (rewrite (HR3 4%bv); exact G4_2).
    lazymatch type of X3 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M3 := mm) in * end.
    pose proof (regs_tbl_restrict w [] _ R3 RT_PM_HT1_3 HTx3 ltac:(vm_compute; reflexivity)) as HT3.
    eapply (pm_leaf0 H HHm LINV LINV_frame AT_FIXWORD 0 _ _ _ (tla_fixword HTL) ((x1, c_endian c)) w _ _ _ _ _ c _ _ _ _ _ msF3 R3 F fc 975296 _);
      [exact OK | exact X3 | exact KR3 | exact VIS3 | exact RF3 | rtf HT3 | rtf HT3 | reflexivity | lia | lia | reflexivity
      | cbn beta iota; split; [exact XR1|]; split; [rewrite (HR3 10%bv); exact (swrap32_sx32A x1 XR1)|]; split; [lia|]; rewrite (HR3 11%bv); exact E27_2
      | vm_compute; reflexivity | vm_compute; reflexivity | ].
    intros msF4 mo4 M4 R4 KR4 VIS4 RF4 X4 KEEP4 MU4 WM4 (r1 & Hr1 & Er1).
    assert (G3_4 : PropExec.getr R4 3%bv = gp) by (rewrite (KEEP4 3%bv ltac:(inb)); exact G3_3).
    assert (G4_4 : PropExec.getr R4 4%bv = tp) by (rewrite (KEEP4 4%bv ltac:(inb)); exact G4_3).
    pose proof (regs_keep w [] R3 R4 RT_PM_HT1_3 HT3 KEEP4) as HT4.
    exact (KV msF4 mo4 M4 R4 r1 KR4 VIS4 RF4 X4 (regs_tbl_restrict w [] _ R4 RT_EE030 HT4 ltac:(vm_compute; reflexivity)) G3_4 G4_4 Hr1 Er1 (eq_trans (KEEP4 27%bv ltac:(inb)) (eq_trans (HR3 27%bv) E27_2))).
  Qed.

End HT1.
