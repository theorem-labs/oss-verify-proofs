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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmInit LbB_PmFin LbB_PmExit2 LbB_DiagStmt LbB_PmDS LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt LbB_PmU2K LbB_PmOL LbB_PmOHK LbB_PmOH3_D.

Section OH3.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis HTL : tabl_leavesA.

  Lemma pm_oh3_Z : forall (w : pmwA H) s LB LBs m mo c msF R F fc (io op t x0 : Z) (Q : config -> Prop),
    pmw_okA H w ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 AT_FIXWORD) fc None m (seg_rom asegs) -> rfull R ->
    PMXA H LINV w s LB LBs m mo c S_OPER TBL_EEF44 [] -> regs_tbl w R RT_EF07Cc ->
    PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    0 <= x0 < 2 ^ 32 -> PropExec.getr R 10%bv = Z_to_bv 64 (sx32A x0) -> PropExec.getr R 11%bv = Z_to_bv 64 (c_endian c) ->
    PropExec.getr R 18%bv = Z_to_bv 64 t -> PropExec.getr R 22%bv = Z_to_bv 64 op -> PropExec.getr R 25%bv = Z_to_bv 64 io ->
    c_endian c = 0 \/ c_endian c = 1 -> t = 0 ->
    (forall msF1 mo1 m1 R1 (word : Z), as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xf2bf8) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXA H LINV w s LB LBs m1 mo1 c S_OPER TBL_EEF44 [] -> regs_tbl w R1 RT_ARM ->
       PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       0 <= word < 2 ^ 32 ->
       PropExec.getr R1 18%bv = Z_to_bv 64 t -> PropExec.getr R1 21%bv = Z_to_bv 64 (sx32A word) ->
       PropExec.getr R1 22%bv = Z_to_bv 64 op -> PropExec.getr R1 25%bv = Z_to_bv 64 io ->
       rw_cells asegs m1 (wa_ff w + 176) [C4 (Z_to_bv 64 word)] -> ffkeepX w [(176, 4)] m m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof using HHbp LINV_frame HTL.
    intros w s LB LBs m mo c msF R F fc io op t x0 Q OK KR0 VIS0 RF0 X0 HT0 G3_0 G4_0 Hx0 E10_0 E11_0
           T18_0 O22_0 I25_0 Hend Ht K.
    exact (@pm_oh3_D HCEIL H HHbp LINV LINV_frame HTL w s LB LBs m mo c msF R F fc io op t x0 Q OK KR0 VIS0 RF0 X0 HT0
             G3_0 G4_0 Hx0 E10_0 E11_0 T18_0 O22_0 I25_0 Hend (or_introl Ht) K).
  Qed.
End OH3.
