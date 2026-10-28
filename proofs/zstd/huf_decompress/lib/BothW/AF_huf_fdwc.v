(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface
     ADepot_iface ARep ALayout AHeapP AFake_iface AFake_arep AFake0k_iface AFake_arep0k AF_fse_rd_iface AF_fse_rd_closedF
     AF_huf_tbl_iface AF_huf_tbl_iface2 AF_huf_bdt AF_huf_sdec AF_huf_fdec AF_huf_fdw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_fdwc () := "C46Stdlib5Lists4List2hdC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission5BothW<AFake_arep0k<fake_flag_AIC5ARocqVerifyHarness?AgentSubmission5BothW<AFake_arep0k?fake_release_AIC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC5ARocqVerifyHarness?AgentSubmission5BothW<AFake_arep0kBstack_malloc_0k_AIK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission5BothWAAF_fse_rd_closedFAfse_readk_closedFC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_bdt@fse_build_proofAC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_sdec9safe_decAC5ARocqVerifyHarness?AgentSubmission5BothW;AF_huf_fdec9fast_decAC5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_fdwAfse_decomp_proofAK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappI47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5BothW;AFake_iface5fflagC5ARocqVerifyHarness?AgentSubmission5BothW;AFake_iface9afake_rngK47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Inst.
  Variable DI : ADepotIface.
  Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
  Hypothesis HL : ahole_laws (AH DI AQ ASEC).
  Variable CI : list (Z * Z).
  Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
  Variable AI : AMallocIface.
  Hypothesis E : AHEAP AI = AHEAP_P (AH DI AQ ASEC).
  Hypothesis EC : aci AI = CI.

  (* [comment removed for export] *)
  Theorem fse_decomp_closedA : forall k, Z.of_nat k < 16382 -> fse_decomp_stmtA AI afake_rng k.
Proof.
intros k HK.
eapply fse_decomp_proofA.
- eapply fake_flag_AI; eassumption.
- eapply fake_release_AI; eassumption.
- eapply stack_malloc_0k_AI; [eassumption ..| lia].
- eapply fse_readk_closedF; [eassumption ..| lia].
- apply fse_build_proofA.
- exact safe_decA.
- exact fast_decA.
Qed.
End Inst.
End CANSEC1.
