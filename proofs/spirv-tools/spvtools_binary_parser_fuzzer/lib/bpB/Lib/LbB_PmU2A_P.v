(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmFin LbB_DiagStmt LbB_PmDS LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmHex LbB_TablStmt LbB_PmLeaf LbB_PmWords LbB_PmVops LbB_PmU2K LbB_PmOL LbB_PmU2A_F.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HUbsan HWord.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablLib.

Section U2A.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis HTL : tabl_leavesA.

  Lemma HHm : asan_rt_hyps H.
  Proof. exact (proj1 HHbp). Qed.

  Lemma pm_u2a_P : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PI0A H LINV w s LB LBs m mo c msF R F fc ->
    4 * c_widx c = 8 * ((4 * wa_n w) / 8) /\ (4 * wa_n w) mod 8 = 4 ->
    (forall msF1 mo1 m1 R1 (r : Z), HS_F07C8 H LINV w s LB LBs m1 mo1 c msF1 R1 F fc r -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q OK P0 [HG HG4] K.
    pose proof P0 as P0c.
    destruct P0 as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz Hic Hend Hw Hbud Hacc Hlt Ha0].
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (B1 & B2 & B3 & B4).
    apply (pm_u2a_head H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK P0c).
    intros msF1 mo1 m1 R1 [X1 KR1 VIS1 RF1 HT1 G3_1 G4_1].
    pose proof (u2a_words H HHbp LINV w s LB LBs m1 mo1 _ _ _ _ _ _ OK X1 (proj1 Hw)) as (WP & W16 & WN & WS1 & WSH).
    pose proof (pmw_apart_ff H HHm _ w _ _ _ _ _ _ _ _ _ _ _ OK X1) as (_ & _ & WFF).
    specialize (WFF (proj1 Hw)).
    unfold sh, ASHADOW_BASE, SHBASE, PM_RF_LO in *.
    destruct (words_rd4 H LINV w s LB LBs m1 mo1 _ _ _ _ _ _ (c_widx c) OK X1 (proj1 Hw) ltac:(lia)) as (bs0 & RD0 & LN0).
    pose proof (bytes_le_to_Z_range4 bs0 LN0) as XR0.
    set (x0 := bytes_le_to_Z bs0) in *.
    set (E1 := Eseed R1 (wenv_vals w ++ [Z_to_bv 64 (c_widx c); Z_to_bv 64 (c_endian c); Z_to_bv 64 (bv_swrap 32 x0)])).
    assert (HE1 : env_world H w E1) by exact (env_world_seed H w R1 _).
    pose proof (ev_world_all H w E1 HE1) as (EV32 & EV33 & EV34 & EV35 & EV36 & _).
    assert (EV41 : edenot E1 (EVar 41) = Z_to_bv 64 (c_widx c)) by reflexivity.
    assert (EV42 : edenot E1 (EVar 42) = Z_to_bv 64 (c_endian c)) by reflexivity.
    assert (EV43 : edenot E1 (EVar 43) = Z_to_bv 64 (bv_swrap 32 x0)) by reflexivity.
    assert (EWA : edenot E1 WADDR = Z_to_bv 64 (wa_words w + 4 * c_widx c)) by (apply ev_waddr; [exact EV36 | exact EV41 | lia | lia | lia]).
    assert (HKX : know_ok asegs E1 m1 (KX_F06E8 4)).
    { unfold KX_F06E8. apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
      - exact (pmk_sh_wordsE_part H HHm LINV w s LB LBs m1 mo1 _ _ _ _ _ _ E1 WADDR (c_widx c) OK X1 (proj1 Hw) EWA HG HG4).
      - eapply pmk_sh_s1disj with (1 := OK) (2 := X1) (3 := HE1) (4 := EWA); lia.
      - eapply pmk_sh_fshdisj with (1 := OK) (2 := X1) (3 := HE1) (4 := EWA); lia. }
    pm_goX HHm LINV_frame OK X1 KR1 VIS1 RF1 HT1 [Z_to_bv 64 (c_widx c); Z_to_bv 64 (c_endian c); Z_to_bv 64 (bv_swrap 32 x0)]
          (KX_F06E8 4) HKX 100%nat [AT_FIXWORD] [false; false; false; false; false; false; false] 41%N
          [OB_INST; OB_FIRST_WORD] [664; 656; 536; 544; 520; 512; 568; 624] (@nil Z) TBL_F07C8 FTBL_F07C8 RT_F07C8.
    { split_scs; u2a_sc X1. }
    intros msF2 mo2 R2 KR2 VIS2 RF2 X2 HTx2 HR2 Hlf2.
    pose proof (regs_tbl_restrict w [] _ R2 RT_F07C8 HTx2 ltac:(vm_compute; reflexivity)) as HT2.
    eapply (pm_u2a_tail H HHbp LINV LINV_frame HTL w s LB LBs _ mo2 c msF2 R2 F fc x0 Q OK X2 KR2 VIS2 RF2 FZ0 HT2);
      [ | | exact XR0 | | | | exact K].
    - rewrite (HR2 3%bv). exact G3_1.
    - rewrite (HR2 4%bv). exact G4_1.
    - rewrite (HR2 10%bv). exact (swrap32_sx32A x0 XR0).
    - rewrite (HR2 11%bv). exact EV42.
    - lia.
  Qed.
End U2A.
