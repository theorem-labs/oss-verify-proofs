(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim StoreOk ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib FxChSep FxChNull FxChFix FxChEnt FxWvC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart.FxChLoop OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_put AXG_put3 AXG_np.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_nf1 AXG_npf AXG_nf6 AXG_gp AXG_gf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_q1 AXG_qf6.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np3.AXG_npscp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf2.AXG_nfscp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_npf OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf6 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gf1 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AXG_gpf OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_qf6.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarve AcSteps AcEntry AcMALp AcHand AcUnwApp0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDepDen AcAst AcHA AcFacts AcCarveP AcMALlib AcPutN AcUnwApp AcTbl.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConv AcConvG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep AcPriHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarveP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcOwnSet AcDenW AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChAdd.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFixXS.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFixXS.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDenW.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCommit.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcNPop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcNPopN.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep2 AcNPopF AcNEnq NqStepZ NqTail AcNEnqLib AcNEnqF0.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcPutAppG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcShapes OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarveP OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPutN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcTblOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConv OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcRdw OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcPriDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarveP.AcStepsOut OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.AcAddOwn OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcOwnSet OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd.AcFixS OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFixXS.AcFixX OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFixXS OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenW.AcRegsEq OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCommit OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AcRunApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AcNPopApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriHA.AcPriGrant OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcStateWf OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep2 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopF OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNEnq OSSVerify.Proofs.fast_float.from_chars.lib.AACB.NqStepZ OSSVerify.Proofs.fast_float.from_chars.lib.AACB.NqTail OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNEnqLib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNEnqF0.
Import ListNotations.

Module AcNEnqD.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim StoreOk ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChFix FxChEnt FxWvC FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_put AXG_put3 AXG_np AXG_nf1 AXG_npf AXG_gp AXG_gf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_q3e.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require NqTail.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_npf OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gf1 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AXG_gpf OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q3.AXG_q2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q3.AXG_q1e OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q3e OSSVerify.Proofs.fast_float.from_chars.lib.AACB.NqTail.AXG_qt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarve AcSteps AcEntry AcMALp AcHand AcUnwApp0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDepDen AcAst AcHA AcFacts AcCarveP AcMALlib AcPutN AcUnwApp AcTbl.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConv AcConvG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep AcPriHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarveP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcOwnSet AcDenW AcConvA AcNPop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcNPopN AcNEnq.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcPutAppG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcShapes OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarveP OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPutN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcTblOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConv OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcRdw OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcPriDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarveP.AcStepsOut OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.AcAddOwn OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcOwnSet OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AcNPopApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AcRunApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNEnq.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import NqStepZ NqTail AcNEnqLib.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.



Section NEnqDrain.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.

(* [comment removed for export] *)
Hypothesis batch_outside : forall mem0 E S M ms model a m0 jP jT, DEN ASEGS LIMIT model0 mem0 E S M ms model -> PRI_on E M a m0 ->
  find_grant (sm_maps M) (p_pg a) PG_SIZE = Some jP -> find_grant (sm_maps M) (p_tg a) TG_SIZE = Some jT ->
  forallb_l (fun R => pri_sep_c (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a R &&& batch_sep (s_facts S) a R) (s_rgs S) = true ->
  1 <= z_qn (pden E a) ->
  forall x, 0 <= x < two64 -> BQ (pden E a) <= x < BQ (pden E a) + 8192 -> outside E (s_rgs S) (Z_to_bv 64 x).

(* [comment removed for export] *)
Hypothesis gbatch_outside : forall mem0 E S M ms model a m0 jP jT, DEN ASEGS LIMIT model0 mem0 E S M ms model -> PRI_on E M a m0 ->
  find_grant (sm_maps M) (p_pg a) PG_SIZE = Some jP -> find_grant (sm_maps M) (p_tg a) TG_SIZE = Some jT ->
  forallb_l (fun R => pri_sep_c (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a R &&& batch_sep_at (s_facts S) a (p_gl a) R) (s_rgs S) = true ->
  1 <= z_gn (pden E a) ->
  forall x, 0 <= x < two64 -> BG (pden E a) <= x < BG (pden E a) + 8192 -> outside E (s_rgs S) (Z_to_bv 64 x).

#[using="Hwx batch_outside gbatch_outside"] Theorem nenq_node_room_drain : forall S M a S' M' a', apost_nenq0 LIMIT S M a = Some (S', M', a') ->
  nq_room S a = true -> nq_nodrain S a = false ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx batch_outside gbatch_outside : LiaFast.U) => LiaFast.u0).
  intros S M a S' M' a' H Hroom Hnd mem0 E ms model T Hd Haw HHA Hk.
  unfold nq_nodrain in Hnd. rewrite Hroom in Hnd. unfold nq_room in Hroom.
  unfold apost_nenq0 in H. cbv zeta in H. rewrite Hroom in H. rewrite Hnd in H.
  apply obool_some in H as (Hon & H).
  apply obind_some in H as (stk & Hstk & H). cbv beta in H.
  apply obind_some in H as (ro & Hro & H). cbv beta in H.
  apply obind_some in H as (ist & Hist & H). cbv beta in H.
  apply obind_some in H as (R & HR & H). cbv beta in H.
  apply obind_some in H as (o & Ho & H). cbv beta in H.
  apply obind_some in H as (cv & Hcv & H). cbv beta in H.
  apply obind_some in H as (jP & HjP & H). cbv beta in H.
  apply obind_some in H as (jT & HjT & H). cbv beta in H.
  apply obind_some in H as (gP & HgP & H). cbv beta in H.
  apply obool_some in H as (Hchk & H).
  apply obind_some in H as (l'' & Hsteps & H). cbv beta in H. injection H as <- <- <-.
  apply andb_prop in Hon as [Hon Hown_eq]. apply andb_prop in Hon as [Hon Hrs]. apply andb_prop in Hon as [Hon Hpc]. apply andb_prop in Hon as [Hon Hlen].
  apply Z.eqb_eq in Hpc. apply rsv_none_b_sound in Hrs. apply Nat.eqb_eq in Hlen.
  apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hown_eq.
  apply andb_prop in Hchk as [Hchk _]. apply andb_prop in Hchk as [Hchk Csep]. apply andb_prop in Hchk as [Hchk Cwo].
  apply andb_prop in Hchk as [Hchk Cwp]. apply andb_prop in Hchk as [Hchk CpX]. apply andb_prop in Hchk as [Hchk CwL].
  apply andb_prop in Hchk as [Hchk Cband]. apply andb_prop in Hchk as [Hchk Cge]. apply andb_prop in Hchk as [Hchk Cdr].
  apply andb_prop in Hchk as [Hchk Csz40]. apply andb_prop in Hchk as [Hchk Cs6]. apply andb_prop in Hchk as [Hchk Ccase]. apply andb_prop in Hchk as [Hchk Csbw].
  apply andb_prop in Hchk as [Hchk Cst]. apply andb_prop in Hchk as [Hchk Cro]. apply andb_prop in Hchk as [Hchk Cwin].
  apply andb_prop in Hchk as [Hchk Csphi]. apply andb_prop in Hchk as [Hchk Csplo]. apply andb_prop in Hchk as [Hchk Cmod].
  apply andb_prop in Hchk as [Hchk Cra]. apply andb_prop in Hchk as [Hchk Cs1]. apply andb_prop in Hchk as [Hchk Ca1].
  apply andb_prop in Hchk as [Cperm Ca0].
  apply andb_prop in Ccase as [Ccase Cqjhi]. apply andb_prop in Ccase as [Cqnhi Cqjlo].
  apply andb_prop in Cdr as [Cdr _]. apply andb_prop in Cdr as [Cdr Cgnhi]. apply andb_prop in Cdr as [Cdr Cgn]. apply andb_prop in Cdr as [Cdr Cmx].
  apply andb_prop in Cdr as [Cdr Cfrm]. apply andb_prop in Cdr as [Cdrlo Cs0].
  apply lin_eqb_eq in Ca0, Ca1, Cs1, Cra, Cs0. apply Z.leb_le in Csplo, Csphi, Cs6, Csz40, Cqnhi, Cqjlo, Cqjhi, Hroom, Cdrlo, Cgnhi.
  set (SPl := rget (s_regs S) (rk 2)) in *. set (szl := rget (s_regs S) (rk 14)) in *. set (s6l := rget (s_regs S) (rk 22)) in *.
  set (front := firstn 3 (carve_rgs cv)) in *. set (rest := skipn 3 (carve_rgs cv)) in *.
  set (L := nq_front S (s_next S) front) in *. set (Sp := nq_rest S rest) in *.
  set (Lb := nq_front S (s_next S + 66) front) in *.
  pose proof (HHA Hon) as HA0.
  assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hlen; discriminate).
  pose proof (ha_pri _ _ _ _ HA0 Hne) as HP0.
  (* [comment removed for export] *)
  pose proof (den_carve ASEGS LIMIT model0 mem0 E S M ms model _ _ _ cv Hd Hcv Cperm) as Hd1.
  assert (EQ1 : with_rgs S (carve_rgs cv) = mrg L Sp).
  { destruct S as [pc0 rg0 rgs0 fs0 nx0 rv0]. cbn [s_pc s_resv] in Hpc, Hrs. subst pc0 rv0.
    unfold with_rgs, mrg, L, Sp, nq_front, nq_rest. cbn [s_pc s_regs s_rgs s_facts s_next s_resv]. unfold front, rest. rewrite firstn_skipn. reflexivity. }
  rewrite EQ1 in Hd1.
  assert (EQb : bump (mrg L Sp) (s_next S + 66) = mrg Lb Sp) by reflexivity.
  pose proof (den_bump ASEGS LIMIT model0 mem0 E _ M ms model (s_next S + 66)%positive Hd1 ltac:(cbn [mrg s_next L nq_front]; lia)) as Hd2.
  rewrite EQb in Hd2.
  (* [comment removed for export] *)
  pose proof (po_inv _ _ _ _ HP0) as HI. unfold INV_A in HI. set (pz := pden E a) in *.
  pose proof (tg_pg_disj LIMIT model0 mem0 E S M ms model a mem0 Hd HP0) as Hdisj. fold pz in Hdisj.
  pose proof (az_geo pz mem0 HI) as G. destruct (q_seps pz mem0 HI Hdisj) as (T1 & S1 & S2 & B0).
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HRG & _ & HF0 & _).
  assert (Eqn : uE E (p_qn a) = z_qn pz) by (symmetry; apply zn_pden).
  assert (Eqb : uE E (p_qb a) = z_qb pz) by (symmetry; apply zn_pden).
  assert (Eqj : uE E (p_qj a) = z_qj pz) by (symmetry; apply zn_pden).
  assert (Eca : uE E (p_ca a) = z_ca pz) by (symmetry; apply zn_pden).
  assert (Esb : uE E (p_sb a) = z_sb pz) by (symmetry; apply zn_pden).
  assert (Egn : uE E (p_gn a) = z_gn pz) by (symmetry; apply zn_pden).
  assert (Egb : uE E (p_gb a) = z_gb pz) by (symmetry; apply zn_pden).
  pose proof (irange_sound E (s_facts S) (p_qn a) HF0) as Rqn. fold (uE E (p_qn a)) in Rqn. rewrite Eqn in Rqn.
  pose proof (irange_sound E (s_facts S) (p_qb a) HF0) as Rqb. fold (uE E (p_qb a)) in Rqb. rewrite Eqb in Rqb.
  pose proof (irange_sound E (s_facts S) (p_gn a) HF0) as Rgn. fold (uE E (p_gn a)) in Rgn. rewrite Egn in Rgn.
  pose proof (irange_sound E (s_facts S) (p_gb a) HF0) as Rgb. fold (uE E (p_gb a)) in Rgb. rewrite Egb in Rgb.
  pose proof (irange_sound E (s_facts S) szl HF0) as Rsz. fold (uE E szl) in Rsz.
  pose proof (irange_sound E (s_facts S) s6l HF0) as Rs6. fold (uE E s6l) in Rs6.
  pose proof (irange_sound E (s_facts S) SPl HF0) as Rsp. fold (uE E SPl) in Rsp.
  assert (Hqn1 : 1 <= z_qn pz <= 1020) by (clear - Rqn Hroom Cqnhi; lia).
  assert (Hal : uE E SPl mod 16 = 0) by (pose proof (fact_implied_ok E _ _ HF0 Cmod) as X; cbn [fact_ok] in X; exact X).
  destruct (iz_q _ _ HI) as [HQ0 HQj]. specialize (HQj ltac:(clear - Hqn1; lia)).
  (* [comment removed for export] *)
  assert (Rqf : fst (irange (s_facts S) (ladd (p_qb a) szl)) <= z_qb pz + uE E szl <= snd (irange (s_facts S) (ladd (p_qb a) szl))).
  { pose proof (irange_sound E (s_facts S) (ladd (p_qb a) szl) HF0) as X. rewrite ladd_u2 in X.
    - fold (uE E (p_qb a)) (uE E szl) in X. rewrite Eqb in X. exact X.
    - fold (uE E (p_qb a)) (uE E szl). rewrite Eqb. destruct HQ0 as (Hqb0 & _).
      assert (Y : snd (irange (s_facts S) szl) <= 2^40) by (first [exact Csz40 | apply Z.leb_le; exact Csz40]). clear - Hqb0 Y Rsz. unfold two64. lia. }
  cbv iota in Cdrlo.
  assert (Hqj0 : 0 <= z_qj pz < 32) by (destruct HQ0 as (_ & _ & [(Q0 & _)|(_ & Q2 & _)]); [clear - Q0 Hqn1; lia | exact Q2]).
  destruct (iz_gq _ _ HI) as [HG0 HGl].
  assert (Hgn0 : 0 <= z_gn pz /\ 0 <= z_gb pz < 2^62) by (destruct HG0 as (X1 & X2 & _); clear - X1 X2; lia).
  assert (Hgl0 : 1 <= z_gn pz -> 0 <= z_gl pz < 32).
  { intros Hg1. destruct HG0 as (_ & _ & _ & _ & _ & _ & _ & _ & [(X0 & _)|(_ & X1 & _)]); [clear - X0 Hg1; lia | exact X1]. }
  (* [comment removed for export] *)
  destruct (rdw IMGP (s_rgs S) (lconst 930608) 8) as [mxl|] eqn:Wmx; [|discriminate].
  destruct (is_const mxl) as [mxs|] eqn:Emx; [|discriminate]. apply andb_prop in Cmx as [Cmx1 Cmx2]. apply Z.leb_le in Cmx1. apply Z.ltb_lt in Cmx2.
  cbv iota in Cmx1.
  pose proof (rdw_sound IMGP IMGP_ok E _ (s_rgs S) (lconst 930608) 8 _ HRG ltac:(lia) Wmx) as RMX.
  rewrite uE_lc in RMX by lia. unfold uE in RMX. rewrite (is_const_u E mxl mxs Emx) in RMX.
  destruct (is_const (rg_size R)) as [zz|] eqn:Ezz; [|discriminate]. apply Z.leb_le in Cfrm.
  (* [comment removed for export] *)
  destruct (rg_hdr_b_sound _ _ _ _ Cwin) as (cw & Pw). destruct (ro_b_sound _ Cro) as (zro & Hzro & Pro).
  destruct (rg_hdr_b_sound _ _ _ _ Cst) as (cs & Pst).
  assert (HwLb : state_wf Lb = true) by (apply (nq_front_wf_mono S (s_next S) (s_next S + 66)%positive front ltac:(lia) CwL)).
  (* [comment removed for export] *)
  destruct (po_gp _ _ _ _ HP0) as (kp & Hgp). destruct (po_gt _ _ _ _ HP0) as (kt & Hgt).
  pose proof (band_hi LIMIT model0 mem0 E S M ms model SPl _ Hd Cband Hgp) as BP.
  pose proof (band_hi LIMIT model0 mem0 E S M ms model SPl _ Hd Cband Hgt) as BT.
  unfold gsz in BP, BT. cbn [fst snd] in BP, BT. unfold PG_SIZE, TG_SIZE in BP, BT. rewrite uE_lc in BP, BT by lia.
  assert (Epg : uE E (p_pg a) = z_pg pz) by (symmetry; apply zn_pden).
  assert (Etg : uE E (p_tg a) = z_tg pz) by (symmetry; apply zn_pden).
  rewrite Epg in BP. rewrite Etg in BT. fold (uE E SPl) in BP, BT.
  (* [comment removed for export] *)
  destruct (forallb_l_and3' _ _ _ _ Csep) as [Csep_b Csep_g]. pose proof (forallb_l_and1 _ _ _ Csep_b) as Csep'.
  assert (HCELL : forall x, 0 <= x < 2^64 -> qdcell pz x -> own_pt E M x /\ outside E (s_rgs (mrg Lb Sp)) (wa x) /\ ~ frz_pt E M x).
  { intros x Hx [[Hq|Hq]|[Hq|(Hg1 & Hq)]].
    - destruct (cb_fp pz mem0 HI Hdisj x ltac:(clear - Hq; lia)) as (F1 & F2 & F3 & F4).
      split; [exact (po_own _ _ _ _ HP0 x Hx F1)|]. split.
      + exact (pri_outside_den LIMIT model0 mem0 E (mrg L Sp) M ms model a mem0 jP jT Hd1 HP0 HjP HjT Csep' x ltac:(unfold two64; lia) F2 F3).
      + exact (pri_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1).
    - destruct (bq_fp pz mem0 HI ltac:(clear - Hqn1; lia) x Hq) as (F1 & F2 & F4).
      split; [exact (po_own _ _ _ _ HP0 x Hx F1)|]. split.
      + exact (batch_outside mem0 E (mrg L Sp) M ms model a mem0 jP jT Hd1 HP0 HjP HjT Csep_b ltac:(fold pz; clear - Hqn1; lia) x ltac:(unfold two64; lia) Hq).
      + exact (pri_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1).
    - destruct (gq_fp pz mem0 HI x Hq) as (F1 & F2 & F3 & F4).
      split; [exact (po_own _ _ _ _ HP0 x Hx F1)|]. split.
      + exact (pri_outside_den LIMIT model0 mem0 E (mrg L Sp) M ms model a mem0 jP jT Hd1 HP0 HjP HjT Csep' x ltac:(unfold two64; lia) F2 F3).
      + exact (pri_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1).
    - destruct (bg_fp pz mem0 HI Hg1 x ltac:(clear - Hq; lia)) as (F1 & F2 & F4).
      split; [exact (po_own _ _ _ _ HP0 x Hx F1)|]. split.
      + destruct (Z.eqb (snd (irange (s_facts S) (p_gn a))) 0) eqn:Egn0; [apply Z.eqb_eq in Egn0; exfalso; clear - Egn0 Rgn Hg1; lia|].
        cbv iota in Csep_g.
        exact (gbatch_outside mem0 E (mrg L Sp) M ms model a mem0 jP jT Hd1 HP0 HjP HjT Csep_g ltac:(fold pz; exact Hg1) x ltac:(unfold two64; lia) ltac:(fold pz; clear - Hq; lia)).
      + exact (pri_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1). }
  (* [comment removed for export] *)
  pose proof (dn_sden _ _ _ _ _ _ _ _ _ Hd2) as Hsd. pose proof (dn_own _ _ _ _ _ _ _ _ _ Hd2) as Hown.
  set (H := Hof E M model) in *. set (msr := restrict H ms) in *.
  pose proof (sden_0 _ _ _ _ Hsd) as Hd0.
  assert (Hsvc : ms_svc_pending ms = None) by (destruct Hd0 as (_ & X & _); exact X).
  assert (Hrv : ms_resv ms = None).
  { destruct Hd0 as (_ & _ & X & _). cbn [mrg s_resv Lb nq_front] in X. cbn [rsv_ok] in X. exact X. }
  set (SP := uE E SPl) in *. set (QC := z_ca pz - 128) in *. set (SB := z_sb pz) in *.
  assert (Ecb : uE E (l_cb a) = QC).
  { unfold l_cb. rewrite uE_laddc_z by (rewrite Eca; unfold two64; clear - B0; lia). rewrite Eca. reflexivity. }
  assert (R1 : getr (ms_regs ms) (Z_to_bv 5 1) = wa 278036).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 1) _ Hd0 Cra). rewrite lden_lconst. reflexivity. }
  assert (R2 : getr (ms_regs ms) (Z_to_bv 5 2) = wa SP).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 2) _ Hd0 eq_refl). unfold wa, SP, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R8 : getr (ms_regs ms) (Z_to_bv 5 8) = wa 930544).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 8) _ Hd0 Cs0). rewrite lden_lconst. reflexivity. }
  assert (R9 : getr (ms_regs ms) (Z_to_bv 5 9) = wa QC).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 9) _ Hd0 Cs1). rewrite <- Ecb. unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = wa QC).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 10) _ Hd0 Ca0). rewrite <- Ecb. unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R14 : getr (ms_regs ms) (Z_to_bv 5 14) = wa (uE E szl)).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 14) _ Hd0 eq_refl). unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R22 : getr (ms_regs ms) (Z_to_bv 5 22) = wa (uE E s6l)).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 22) _ Hd0 eq_refl). unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  (* [comment removed for export] *)
  pose proof (mrg_rg0 E Lb Sp msr 0%nat _ Hd0 Pw) as Rw.
  assert (HSPr : 2^46 + 8192 <= SP <= 2^47) by (clear - Rsp Csplo Csphi; unfold SP; lia).
  assert (Ebw : bv_unsigned (lden E (laddc SPl (-2064))) = SP - 2064) by (rewrite lden_laddc; fold (uE E SPl); fold SP; rewrite u_small64; unfold two64; clear - HSPr; lia).
  assert (Bw : forall x, SP - 2064 <= x < SP -> rd1 ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None /\ wview ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None).
  { intros x Hx. apply (rg_rw_pt _ _ _ x Rw eq_refl). cbn [rg_base]. rewrite Ebw. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; clear; lia). clear - Hx. lia. }
  assert (Hstko : stk_ok ASEGS (ms_mem msr) (wa SP) 2048).
  { intros a0 k Ha Hk'. rewrite u_wa_small in Ha, Hk' by (clear - HSPr; lia). apply store_ok_of_all; [pose proof (bv_unsigned_in_range _ a0) as Ra0; clear - Ra0 Ha Hk' HSPr; lia|].
    intros x Hx. pose proof (bv_unsigned_in_range _ x) as Rx. destruct (Bw (bv_unsigned x) ltac:(clear - Hx Ha Hk'; lia)) as [_ W]. rewrite Z_to_bv_bv_unsigned in W. exact W. }
  (* [comment removed for export] *)
  assert (Bf : forall x, SP <= x < SP + 16 -> rd1 ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None /\ wview ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None).
  { intros x Hx. rewrite Forall_forall in HRG. pose proof (HRG R (nth_error_In _ _ HR)) as RR.
    assert (HkR : rg_kind R = RW).
    { pose proof Hcv as X. unfold carve_of in X. rewrite HR in X. destruct R as [b0 z0 k0 c0]. destruct k0; try discriminate. reflexivity. }
    destruct (lin_off_sound E SPl (rg_base R) o Ho) as [_ Ho0].
    pose proof RR as Hrsz. destruct Hrsz as (_ & Hrsz & _). cbv zeta in Hrsz.
    assert (Ezr : rsz E R = zz) by (unfold rsz; exact (is_const_u E _ _ Ezz)).
    pose proof (FxChFix.lin_off_u E SPl (rg_base R) o Ho ltac:(rewrite Ezr in Hrsz; clear - Hrsz Cfrm Ho0; unfold two64 in *; lia)) as Eo. fold (uE E SPl) in Eo. fold SP in Eo.
    apply (rg_rw_pt _ _ _ x RR ltac:(rewrite HkR; reflexivity)). rewrite Ezr. clear - Hx Eo Cfrm Ho0. lia. }
  (* [comment removed for export] *)
  assert (Hcell : forall x, 0 <= x < 2^64 -> qdcell pz x -> ms_mem msr (wa x) = mem0 (wa x) /\ H (wa x) = false).
  { intros x Hx Hc0. destruct (HCELL x Hx Hc0) as ((p & Hp & Hpw) & Hout & _). pose proof (Hown p Hp x Hpw) as [Hv Hm].
    fold H in Hv. unfold wa. split; [|exact Hv]. cbn [msr restrict ms_mem]. unfold mrestrict. rewrite Hv. apply Hm. exact Hout. }
  assert (B1 : 0 <= QC /\ QC + 32 <= 2^63 /\ 0 <= SB /\ SB + 137438953472 <= 2^63) by (unfold QC, SB; clear - B0; lia).
  assert (IQ : q_inv (ms_mem msr) QC SB (z_qj pz) (z_qn pz) (z_qb pz)).
  { apply (q_inv_frame mem0); [clear - B1; lia | clear - B1; lia | clear - B1; lia | clear - B1; lia | | | exact HQ0].
    - intros x Hx. apply (Hcell x); [clear - Hx B1; lia | left; left; unfold QC in Hx; clear - Hx; lia].
    - intros _ x Hx. apply (Hcell x); [clear - Hx B1 Hqj0; lia | left; right; unfold BQ; exact Hx]. }
  assert (Hwq32 : wr (ms_mem msr) QC 32).
  { apply (wr_frame mem0); [clear - B1; lia | clear - B1; lia | |].
    - intros x Hx. apply (Hcell x); [clear - Hx B1; lia | left; left; unfold QC in Hx; clear - Hx; lia].
    - intros d k Hd' Hk'. replace (QC + d) with (z_ca pz - 128 + d) by (unfold QC; ring). apply (iz_wc _ _ HI); lia. }
  assert (Hwq : wr (ms_mem msr) (QC + 24) 8).
  { intros d k Hd' Hk'. replace (QC + 24 + d) with (QC + (24 + d)) by ring. apply Hwq32; lia. }
  assert (IGQ : gq_inv (ms_mem msr) SB (z_gn pz) (z_gl pz) (z_gb pz) mxs).
  { apply gq_inv_of_o; [|clear - Cmx1 Cmx2 Rqb Rsz Rgb Hgn0 HQ0 Rqf; destruct HQ0 as (X & _); pose proof (uE_range E szl); lia | exact RMX].
    apply (gq_inv_o_frame mem0); [clear - B1; lia | clear - B1; lia | | exact HG0].
    intros x [Hx|(Hg1 & Hx)]; apply (Hcell x).
    - clear - Hx. lia.
    - right. left. exact Hx.
    - specialize (Hgl0 Hg1). clear - Hx B1 Hgl0. lia.
    - right. right. split; [exact Hg1 | unfold BG; exact Hx]. }
  set (mp := bv_unsigned (getr (ms_regs ms) (Z_to_bv 5 13))).
  set (sz := uE E szl) in *. set (mx := uE E s6l) in *.
  assert (Hnum : 0 <= sz <= 2^40 /\ 0 <= mp < 2^64 /\ 0 <= mx < 2^62 /\ z_qb pz + sz < 2^62 /\ mx + 1 <= z_qb pz + sz /\ z_qb pz + sz + z_gb pz <= mxs).
  { pose proof (uE_range E szl) as U1. pose proof (uE_range E s6l) as U2. pose proof (bv_unsigned_in_range _ (getr (ms_regs ms) (Z_to_bv 5 13))) as U3.
    destruct HQ0 as (Hqb0 & _). fold mp in U3. fold sz in U1. fold mx in U2.
    clear - U1 U2 U3 Hqb0 Hgn0 Rqb Rgb Rsz Rs6 Cs6 Csz40 Cdrlo Cmx1 Cmx2 Rqf. unfold two64 in *. change (bv_modulus 64) with 18446744073709551616 in U3. lia. }
  assert (HQCf : ((4176 <= QC /\ QC + 4016 <= 65536) \/ 6537296 <= QC) /\ QC + 32 <= SP - 2048).
  { pose proof (iz_ca _ _ HI) as (X1 & X2 & X3). fold pz in X1, X2, X3. unfold QC. split; [clear - X1; lia | clear - G BT HSPr; fold SP in BT; lia]. }
  assert (HSBf : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048).
  { pose proof (iz_sb _ _ HI) as (X1 & X2). fold pz in X1, X2. unfold SB. split; [exact X1|]. split; [exact X2 | clear - G BP B0; fold SP in BP; lia]. }
  assert (HSEPf : QC + 32 <= SB \/ SB + 137438953472 + 4096 <= QC) by (unfold QC, SB; clear - T1 B0; lia).
  (* [comment removed for export] *)
  destruct (@qroom_e (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_rom ms) (ms_mem msr) (ms_regs ms) QC SB (z_qj pz) (z_qn pz) (z_qb pz) sz mp mx SP IQ Hqn1)
    as (Ra & m1 & Hms1 & HK1 & HQ1 & _ & Hfr1 & Hgr1).
  all: try (replace (1%bv : reg) with (Z_to_bv 5 1) by (apply bv_eq; reflexivity); exact R1).
  all: try (replace (2%bv : reg) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity); exact R2).
  all: try (replace (9%bv : reg) with (Z_to_bv 5 9) by (apply bv_eq; reflexivity); exact R9).
  all: try (replace (10%bv : reg) with (Z_to_bv 5 10) by (apply bv_eq; reflexivity); exact R10).
  all: try (replace (13%bv : reg) with (Z_to_bv 5 13) by (apply bv_eq; reflexivity); unfold mp, wa; rewrite Z_to_bv_bv_unsigned; reflexivity).
  all: try (replace (14%bv : reg) with (Z_to_bv 5 14) by (apply bv_eq; reflexivity); exact R14).
  all: try (replace (22%bv : reg) with (Z_to_bv 5 22) by (apply bv_eq; reflexivity); exact R22).
  all: try exact Hstko. all: try exact Hwq.
  all: try (split; [clear - HSPr; lia | exact Hal]).
  all: try exact HQCf. all: try exact HSBf. all: try exact HSEPf.
  { clear - Hnum. lia. }
  (* [comment removed for export] *)
  set (B := SB + 103079215104 + 8192 * z_qj pz) in *.
  assert (Hfr1' : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ (QC + 24 <= x < QC + 32) -> ~ (B + 8 <= x < B + 8192) -> m1 (wa x) = ms_mem msr (wa x)).
  { intros x Hx N0 N1 N2. apply Hfr1; [exact Hx | exact N0 | exact N1 | clear - N2; lia | clear - N2 Hqn1; lia]. }
  assert (IGQ1 : gq_inv m1 SB (z_gn pz) (z_gl pz) (z_gb pz) mxs).
  { apply gq_inv_of_o; [|clear - Hnum Hgn0 Cmx2 HQ0; destruct HQ0 as (X & _); lia |].
    - apply (gq_inv_o_frame (ms_mem msr)); [clear - B1; lia | clear - B1; lia | | exact (gq_inv_to_o _ _ _ _ _ _ IGQ)].
      intros x [Hx|(Hg1 & Hx)]; apply Hfr1'.
      + clear - Hx. lia.
      + clear - Hx HSPr. lia.
      + clear - Hx HQCf. lia.
      + unfold B. clear - Hx HSBf Hqj0. lia.
      + specialize (Hgl0 Hg1). clear - Hx B1 Hgl0. lia.
      + specialize (Hgl0 Hg1). clear - Hx HSBf Hgl0. lia.
      + specialize (Hgl0 Hg1). clear - Hx HSEPf HQCf Hgl0 B1. lia.
      + specialize (Hgl0 Hg1). unfold B. clear - Hx Hgl0 Hqj0. lia.
    - apply (rd_frame (ms_mem msr)); [lia | cbn; lia | | exact RMX]. intros x Hx. cbn in Hx. apply Hfr1'.
      + clear - Hx. lia.
      + clear - Hx HSPr. lia.
      + clear - Hx HQCf. lia.
      + unfold B. clear - Hx HSBf Hqj0. lia. }
  assert (Hstk1 : stk_ok ASEGS m1 (wa SP) 2048) by exact (stk_ok_grows ASEGS _ _ _ _ Hstko Hgr1).
  assert (Hwq1 : wr m1 QC 32) by (intros d k Hd' Hk'; apply (store_ok_mono ASEGS k (ms_mem msr) m1 _ Hgr1); exact (Hwq32 d k Hd' Hk')).
  assert (Bf1 : forall x, SP <= x < SP + 16 -> rd1 ASEGS m1 (Z_to_bv 64 x) <> None).
  { intros x Hx. destruct (Bf x Hx) as [X1 X2]. exact (proj1 (grows_rw ASEGS (ms_mem msr) m1 _ Hgr1 X1 X2)). }
  destruct (rdn_some m1 SP 8 ltac:(clear - HSPr; lia) ltac:(cbn; unfold two64; clear - HSPr; lia)) as (bs2 & Hbs2).
  { intros i Hi. cbn in Hi. apply Bf1. clear - Hi. lia. }
  destruct (rd_exists m1 SP 8 bs2 ltac:(lia) Hbs2) as (pa2 & Hpa2a & Hpa2b & S0).
  destruct (rdn_some m1 (SP + 8) 8 ltac:(clear - HSPr; lia) ltac:(cbn; unfold two64; clear - HSPr; lia)) as (bs3 & Hbs3).
  { intros i Hi. cbn in Hi. apply Bf1. clear - Hi. lia. }
  destruct (rd_exists m1 (SP + 8) 8 bs3 ltac:(lia) Hbs3) as (pa3 & Hpa3a & Hpa3b & S8).
  (* [comment removed for export] *)
  destruct (@qtail_d (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_rom ms) m1 Ra QC SB (z_qj pz) (z_qn pz + 1) (z_qb pz + sz) mx (z_gn pz) (z_gl pz) (z_gb pz) mxs SP pa2 pa3
              HQ1 ltac:(clear - Hqn1; lia) IGQ1 ltac:(clear - Rgn Cgnhi; lia))
    as (Rb & m2 & Hms2 & HRb1 & HK2 & HQ2 & HG2 & Hfr2 & Hgr2).
  1: { replace (2%bv : reg) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). rewrite (HK1 2%nat ltac:(clear; unfold KQ; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])). exact R2. }
  1: { replace (8%bv : reg) with (Z_to_bv 5 (Z.of_nat 8)) by (apply bv_eq; reflexivity). rewrite (HK1 8%nat ltac:(clear; unfold KQ; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])). exact R8. }
  1: { replace (9%bv : reg) with (Z_to_bv 5 (Z.of_nat 9)) by (apply bv_eq; reflexivity). rewrite (HK1 9%nat ltac:(clear; unfold KQ; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])). exact R9. }
  1: { replace (22%bv : reg) with (Z_to_bv 5 (Z.of_nat 22)) by (apply bv_eq; reflexivity). rewrite (HK1 22%nat ltac:(clear; unfold KQ; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])). exact R22. }
  2: exact Hstk1. 2: exact S0. 2: exact S8. 3: exact HQCf. 3: exact HSBf. 3: exact HSEPf. 4: exact Hwq1.
  { clear - HSPr. lia. }
  { clear - Hpa2a Hpa2b Hpa3a Hpa3b. lia. }
  { clear - Hnum. lia. }
  (* [comment removed for export] *)
  pose proof (msteps_trans ASEGS _ _ _ Hms1 Hms2) as Hms.
  assert (Hgr : mem_grows (ms_mem msr) m2) by exact (mem_grows_trans _ _ _ Hgr1 Hgr2).
  assert (Hpc0 : ms_pc_val ms = wa 0x43e20) by (destruct Hd0 as (X & _); cbn [mrg s_pc Lb nq_front] in X; exact X).
  rewrite <- Hpc0 in Hms.
  assert (Est : uE E (laddc (p_tg a) 2872) = z_tg pz + 2872).
  { rewrite uE_laddc_z by (rewrite Etg; unfold two64; clear - G; lia). rewrite Etg. reflexivity. }
  assert (Hfr : forall x, 0 <= x < 2^64 -> ~ (SP - 2064 <= x < SP) -> ~ qdcell pz x -> m2 (wa x) = ms_mem msr (wa x)).
  { intros x Hx N0 Nq. rewrite Hfr2; [apply Hfr1'; [exact Hx | clear - N0; lia | |] | exact Hx | clear - N0; lia | | |].
    - intros Hc0. apply Nq. left. left. unfold QC in Hc0. clear - Hc0. lia.
    - intros Hc0. apply Nq. left. right. unfold BQ. fold SB. fold B. clear - Hc0. lia.
    - intros Hc0. apply Nq. left. left. unfold QC in Hc0. clear - Hc0. lia.
    - intros Hc0. apply Nq. right. left. exact Hc0.
    - intros (Hg1 & Hc0). apply Nq. right. right. split; [exact Hg1 | unfold BG; fold SB; exact Hc0]. }
  assert (HKb : forall k, In k [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat -> getr Rb (Z_to_bv 5 (Z.of_nat k)) = getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk'. rewrite (HK2 k Hk'). apply HK1. clear - Hk'. unfold KQ. cbn [In] in *. intuition. }
  apply (den_run_app cfg LIMIT model0 Hwx mem0 Lb Sp E M ms model T SPl (laddc (p_tg a) 2872) 0%nat 2%nat cw cs 0x43d4c KT2k
           [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat Rb m2 (qdcell pz) 2064 ltac:(lia) Hd2 HwLb eq_refl Pw Pst).
  - fold SP. clear - HSPr. lia.
  - rewrite Est. clear - G BT HSPr. fold SP in BT. lia.
  - exact kt2_cases.
  - exact Hms.
  - exact HKb.
  - exact HCELL.
  - intros x Hx Hw _ Hq. apply Hfr; [exact Hx | fold SP in Hw; exact Hw | exact Hq].
  - exact Hgr.
  - intros E' ms' model' HD' Ha' Hfz' Hrr Hvis.
    set (Lh := hand_post Lb 0x43d4c KT2k [0%nat; 2%nat]) in *.
    set (hyb := hyb_p (qdcell_b pz) (ms_mem ms') mem0).
    assert (HwfM : sm_wf (s_next Lb) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd2).
    assert (HbwS : bases_wf (s_next Lb) (s_rgs (mrg Lb Sp)) = true) by exact (dn_bases _ _ _ _ _ _ _ _ _ Hd2).
    assert (Hsh : shape (s_rgs (mrg Lh Sp)) = shape (s_rgs (mrg Lb Sp))).
    { cbn [mrg s_rgs]. unfold Lh, hand_post. cbn [s_rgs]. unfold shape. rewrite !map_app. f_equal.
      pose proof (empty_at_shape [0%nat; 2%nat] (s_rgs Lb) 0) as Hs. unfold shape in Hs. exact Hs. }
    assert (Hnwin : forall w, outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w) -> 0 <= w < two64 -> ~ (SP - 2064 <= w < SP)).
    { intros w Hout Hw Hc0. unfold outside in Hout. rewrite Forall_forall in Hout. cbn [mrg s_rgs] in Hout.
      specialize (Hout _ ltac:(apply in_or_app; left; exact (nth_error_In _ _ Pw))). cbn [rg_base] in Hout.
      unfold rsz in Hout. cbn [rg_size] in Hout. rewrite lden_lconst, (u_small64 2064) in Hout by (unfold two64; clear; lia).
      rewrite Ebw in Hout. rewrite u_small64 in Hout by exact Hw. clear - Hout Hc0. lia. }
    assert (Hkeep : forall w, 0 <= w < two64 -> own_pt E M w -> outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w) ->
              ~ qdcell pz w -> ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
    { intros w Hw (q & Hq & Hqw) Hout Hnc. destruct (Hown q Hq w Hqw) as [Hv Hm]. rewrite <- (Hm Hout). fold H in Hv.
      rewrite (Hvis _ Hv). change (Z_to_bv 64 w) with (wa w).
      rewrite Hfr; [cbn [msr restrict ms_mem]; unfold mrestrict, wa; rewrite Hv; reflexivity | unfold two64 in Hw; exact Hw | exact (Hnwin w Hout Hw) | exact Hnc]. }
    assert (Hfrzn : forall w, frz_pt E M w -> hyb (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
    { intros w Hw. unfold hyb, hyb_p. destruct (qdcell_b _ _); [exact (Hfz' w Hw) | reflexivity]. }
    assert (Hw64 : forall w, own_pt E M w -> 0 <= w < two64).
    { intros w Hw0. destruct (Z_lt_le_dec w two64) as [X|X].
      - destruct Hw0 as (q & Hq & Hqw). pose proof (uE_range E (fst q)) as Uq. clear - Uq Hqw X. lia.
      - exfalso. destruct (ha_ownx _ _ _ _ HA0 w (own_pt_a_M E M a w Hown_eq Hw0)) as [Dc|[_ Pf]].
        + destruct HA0 as [(n0 & F0 & st0 & I0 & _) _ _ _ _ _ _]. destruct I0 as [_ _ _ D1r _ _ _ _ _ B1r _ _ _].
          unfold dcov in Dc. unfold two64 in X. clear - Dc X D1r B1r. lia.
        + pose proof (pri_foot_rng E a mem0 HI w Pf) as Pr. unfold two64 in X. clear - Pr X. lia. }
    assert (HD3 : DEN ASEGS LIMIT model0 hyb E' (mrg Lh Sp) M ms' model').
    { apply (den_snap ASEGS LIMIT model0 (ms_mem ms') hyb E' _ M ms' model' HD').
      - intros w Hw. pose proof (proj1 (frz_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw) as Hw0.
        rewrite (Hfrzn w Hw0). symmetry. exact (Hfz' w Hw0).
      - intros w Hw Hout. unfold hyb, hyb_p.
        destruct (qdcell_b pz (bv_unsigned (Z_to_bv 64 w))) eqn:Eb; [reflexivity|].
        assert (Hw0 : own_pt E M w) by exact (proj1 (own_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw).
        assert (Hout0 : outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w)) by exact (outside_agree_shape _ E E' _ _ _ HbwS Ha' Hsh Hout).
        pose proof (Hw64 w Hw0) as Hw6.
        rewrite u_small64 in Eb by exact Hw6. symmetry. apply (Hkeep w Hw6 Hw0 Hout0).
        intros Hn. apply qdcell_b_spec in Hn. congruence. }
    (* [comment removed for export] *)
    assert (Hch : forall E'', agree (s_next (mrg Lh Sp)) E' E'' -> lden E'' (lconst 0x43d4c) = lden E'' (rget (s_regs (mrg Lh Sp)) (rk 1))).
    { intros E'' Ha''. pose proof (dn_sden _ _ _ _ _ _ _ _ _ HD3 E'' Ha'') as (_ & _ & _ & Hregs & _).
      specialize (Hregs (Z_to_bv 5 1)). cbn [restrict ms_regs] in Hregs. change (rkey (Z_to_bv 5 1)) with (rk 1) in Hregs.
      rewrite <- Hregs, Hrr. rewrite lden_lconst. replace (Z_to_bv 5 1) with (1%bv : reg) by (apply bv_eq; reflexivity). rewrite HRb1. reflexivity. }
    assert (Hrk : rk 1 <> xH) by (intros Hc0; vm_compute in Hc0; discriminate).
    pose proof (den_reg_eq ASEGS LIMIT model0 hyb E' _ M ms' model' (rk 1) (lconst 0x43d4c) HD3 Hrk Hch) as HD4.
    set (X := with_reg (mrg Lh Sp) (rk 1) (lconst 0x43d4c)) in *.
    pose proof (den_uncarve ASEGS LIMIT model0 hyb E' X M ms' model' _ _ l'' HD4 CpX Hsteps) as HD5.
    assert (HawLb : awf (s_next Lb) a = true) by (apply (awf_mono (s_next S)); [cbn [Lb nq_front s_next]; lia | exact Haw]).
    assert (Epz' : pden E' a = pz) by exact (pden_agree (s_next Lb) E E' a HawLb Ha').
    (* [comment removed for export] *)
    set (hyb1 := hyb_p (qdcell_b pz) m1 mem0).
    assert (Hh1_in : forall x, 0 <= x < 2^64 -> qdcell pz x -> hyb1 (wa x) = m1 (wa x)).
    { intros x Hx Hn. unfold hyb1, hyb_p. rewrite u_wa_small by exact Hx. rewrite (proj2 (qdcell_b_spec _ _) Hn). reflexivity. }
    assert (Hh1_out : forall x, 0 <= x < 2^64 -> ~ qdcell pz x -> hyb1 (wa x) = mem0 (wa x)).
    { intros x Hx Hn. unfold hyb1, hyb_p. rewrite u_wa_small by exact Hx.
      destruct (qdcell_b pz x) eqn:Eb; [exfalso; apply Hn; apply qdcell_b_spec; exact Eb | reflexivity]. }
    assert (Hhyb_out : forall x, 0 <= x < 2^64 -> ~ qdcell pz x -> hyb (wa x) = mem0 (wa x)).
    { intros x Hx Hn. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx.
      destruct (qdcell_b pz x) eqn:Eb; [exfalso; apply Hn; apply qdcell_b_spec; exact Eb | reflexivity]. }
    assert (Hhyb_m2 : forall x, 0 <= x < 2^64 -> qdcell pz x -> hyb (wa x) = m2 (wa x)).
    { intros x Hx Hn. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx. rewrite (proj2 (qdcell_b_spec _ _) Hn). apply Hvis. exact (proj2 (Hcell x Hx Hn)). }
    (* [comment removed for export] *)
    assert (Hfoot_lo : forall x, pri_foot_z pz x -> 0 <= x < SP - 2064).
    { intros x Hf. pose proof (pri_foot_rng E a mem0 HI x Hf) as Hxr. split; [clear - Hxr; lia|].
      destruct Hf as [Hf|[Hf|[Hf|(c & Hc & Hf)]]].
      - clear - Hf G BT. fold SP in BT. lia.
      - clear - Hf G BP B0. fold SP in BP. fold SB in Hf, B0. lia.
      - clear - Hf HSPr. lia.
      - pose proof (in_cls_rng c Hc) as Hcr. destruct (cls_jb pz mem0 HI c Hc) as (_ & _ & _ & Kz).
        clear - Hf G BP B0 S1 Hcr Kz. fold SP in BP. fold SB in Hf, B0, G. lia. }
    set (pz0 := qz_room pz sz).
    pose proof (iz_len _ _ HI) as Hlenz.
    (* [comment removed for export] *)
    assert (HI1 : INV_Az pz0 hyb1).
    { apply (INV_Az_qroom pz mem0 hyb1 sz HI Hdisj ltac:(clear - Hqn1; lia)).
      - apply (q_inv_frame m1); [clear - B1; lia | clear - B1; lia | clear - B1; lia | clear - B1; lia | | | exact HQ1].
        + intros x Hx. apply Hh1_in; [clear - Hx B1; lia | left; left; unfold QC in Hx; clear - Hx; lia].
        + intros _ x Hx. apply Hh1_in; [clear - Hx B1 Hqj0; lia | left; right; unfold BQ; exact Hx].
      - intros x Hx. rewrite (wview_same m1 hyb1) by (apply Hh1_in; [clear - Hx B0; lia | left; left; clear - Hx; lia]).
        apply (wr_byte m1 QC 32 x); [clear - B1; lia | clear - B1; lia | exact Hwq1 | unfold QC; clear - Hx; lia].
      - intros x Hf N1 N2. destruct (Hfoot_lo x Hf) as [Hx0 Hxlo].
        destruct (qdcell_b pz x) eqn:Eb; [|apply Hh1_out; [clear - Hx0 Hxlo HSPr; lia | intros Hn; apply qdcell_b_spec in Hn; congruence]].
        apply qdcell_b_spec in Eb. rewrite (Hh1_in x ltac:(clear - Hx0 Hxlo HSPr; lia) Eb).
        rewrite Hfr1'; [exact (proj1 (Hcell x ltac:(clear - Hx0 Hxlo HSPr; lia) Eb)) | clear - Hx0 Hxlo HSPr; lia | clear - Hxlo; lia | unfold QC; clear - N1; lia |].
        unfold BQ in N2. fold SB in N2. fold B in N2. exact N2. }
    (* [comment removed for export] *)
    assert (Ez0 : z_ca pz0 = z_ca pz /\ z_sb pz0 = SB /\ z_qj pz0 = z_qj pz /\ z_qn pz0 = z_qn pz + 1 /\ z_qb pz0 = z_qb pz + sz /\
                  z_gn pz0 = z_gn pz /\ z_gl pz0 = z_gl pz /\ z_gb pz0 = z_gb pz /\ z_tg pz0 = z_tg pz /\ z_pg pz0 = z_pg pz).
    { unfold pz0. rewrite (qroom_ca pz sz Hlenz), (qroom_sb pz sz Hlenz), (qroom_qj pz sz Hlenz), (qroom_qn pz sz Hlenz), (qroom_qb pz sz Hlenz),
        (qroom_gn pz sz Hlenz), (qroom_gl pz sz Hlenz), (qroom_gb pz sz Hlenz), (qroom_tg pz sz Hlenz), (qroom_pg pz sz Hlenz). repeat split; reflexivity. }
    destruct Ez0 as (Zca & Zsb & Zqj & Zqn & Zqb & Zgn & Zgl & Zgb & Ztg & Zpg).
    assert (HIz' : INV_Az (qz_drain pz0) hyb).
    { apply (INV_Az_qdrain pz0 hyb1 hyb HI1); rewrite ?Zca, ?Zsb, ?Zqj, ?Zqn, ?Zqb, ?Zgn, ?Zgl, ?Zgb, ?Ztg, ?Zpg.
      - exact Hdisj.
      - clear - Hqn1. lia.
      - fold QC. apply (q_inv_frame m2); [clear - B1; lia | clear - B1; lia | clear - B1; lia | clear - B1; lia | | | exact HQ2].
        + intros x Hx. apply Hhyb_m2; [clear - Hx B1; lia | left; left; unfold QC in Hx; clear - Hx; lia].
        + intros Hc0. exfalso. clear - Hc0. lia.
      - replace (z_gb pz + (z_qb pz + sz)) with (z_qb pz + sz + z_gb pz) by ring.
        apply (gq_inv_o_frame m2); [clear - B1; lia | clear - B1; lia | | exact (gq_inv_to_o _ _ _ _ _ _ HG2)].
        intros x [Hx|(_ & Hx)]; apply Hhyb_m2.
        + clear - Hx. lia.
        + right. left. exact Hx.
        + clear - Hx B1 Hqj0. lia.
        + left. right. unfold BQ. fold SB. clear - Hx. lia.
      - intros x Hx. rewrite (wview_same m2 hyb) by (apply Hhyb_m2; [clear - Hx B0; lia | left; left; clear - Hx; lia]).
        apply (wr_byte m2 QC 32 x); [clear - B1; lia | clear - B1; lia | | unfold QC; clear - Hx; lia].
        intros d k Hd' Hk'. apply (store_ok_mono ASEGS k m1 m2 _ Hgr2). exact (Hwq1 d k Hd' Hk').
      - intros x Hf N1 N2 N3. apply (qroom_foot pz sz Hlenz) in Hf. destruct (Hfoot_lo x Hf) as [Hx0 Hxlo].
        assert (Hx64 : 0 <= x < 2^64) by (clear - Hx0 Hxlo HSPr; lia).
        destruct (qdcell_b pz x) eqn:Eb.
        + apply qdcell_b_spec in Eb. rewrite (Hhyb_m2 x Hx64 Eb), (Hh1_in x Hx64 Eb).
          apply Hfr2; [exact Hx64 | clear - Hxlo; lia | unfold QC; clear - N1; lia | exact N2 |].
          intros (Hg1 & Hc0). apply N3. split; [exact Hg1 | unfold BG; rewrite Zsb, Zgl; exact Hc0].
        + assert (Hn : ~ qdcell pz x) by (intros Hn; apply qdcell_b_spec in Hn; congruence).
          rewrite (Hhyb_out x Hx64 Hn), (Hh1_out x Hx64 Hn). reflexivity. }
    set (pri' := q_step_drain (q_step_room a szl) a (p_qj a) (ladd (p_qb a) szl)) in *.
    assert (Ha'' : a_qstep a pri' = a_with a pri') by reflexivity.
    set (a' := a_qstep a pri') in *.
    assert (Hwsz : lwf (s_next Lb) szl = true).
    { pose proof HwLb as XW. unfold state_wf in XW. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _].
      exact (regs_wf_n_spec _ _ 31 XW 14%nat ltac:(lia)). }
    assert (Epz2 : pden E' a' = qz_drain pz0).
    { unfold a', pri'. rewrite (pden_qroom_drain E' a szl Hlen); rewrite ?Epz', ?(uE_agree (s_next Lb) E E' szl Hwsz Ha'); fold sz.
      - reflexivity.
      - clear - Hqn1. unfold two64. lia.
      - clear - Hnum HQ0. destruct HQ0 as (X & _). unfold two64. lia.
      - clear - Rgn Cgnhi Hgn0. unfold two64. lia.
      - clear - Hnum Hgn0 HQ0. destruct HQ0 as (X & _). unfold two64. lia. }
    assert (Hne' : pri' <> []).
    { intros Hn. pose proof (f_equal (@List.length lin) Hn) as XL. unfold pri', q_step_drain, q_step_room in XL. rewrite !set_nth_length, Hlen in XL. discriminate. }
    assert (Hbase : forall k, (k < 5)%nat -> nth k pri' lc0 = nth k (a_pri a) lc0).
    { intros k Hk5. unfold pri', q_step_drain, q_step_room.
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia). replace (Nat.eqb k 70) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia). replace (Nat.eqb k 69) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia). replace (Nat.eqb k 68) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia). replace (Nat.eqb k 67) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia). replace (Nat.eqb k 66) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia). replace (Nat.eqb k 67) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite Hlen; unfold PRI_LEN; clear; lia). replace (Nat.eqb k 66) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia). reflexivity. }
    assert (Hl0 : List.length pz0 = PRI_LEN) by exact (qroom_len pz sz Hlenz).
    assert (Hfoot_eq : forall x, pri_foot_z (qz_drain pz0) x <-> pri_foot_z pz x).
    { intros x. rewrite (qdrain_foot pz0 Hl0 x). exact (qroom_foot pz sz Hlenz x). }
    assert (Hmono : forall x, pri_foot_z (pden E a) x -> pri_foot_z (pden E' (a_with a pri')) x).
    { intros x Hf. change (a_with a pri') with a'. rewrite Epz2. apply Hfoot_eq. exact Hf. }
    assert (Hdepf : forall x, 0 <= x < 2^64 -> downed (dD1 E a) (dB1 E a) x -> hyb (wa x) = mem0 (wa x)).
    { intros x Hx Hdw. apply (Hhyb_out x Hx). intros Hn.
      assert (F1 : pri_foot E a x).
      { destruct Hn as [[Hn|Hn]|[Hn|(Hg1 & Hn)]].
        - exact (proj1 (cb_fp pz mem0 HI Hdisj x ltac:(clear - Hn; lia))).
        - exact (proj1 (bq_fp pz mem0 HI ltac:(clear - Hqn1; lia) x Hn)).
        - exact (proj1 (gq_fp pz mem0 HI x Hn)).
        - exact (proj1 (bg_fp pz mem0 HI Hg1 x ltac:(clear - Hn; lia))). }
      exact (pri_not_downed LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1 Hdw). }
    assert (Hext_step : forall b z, ext_sem (pden E a) b z -> ext_sem (pden E' (a_with a pri')) b z).
    { intros b z Hbz. change (a_with a pri') with a'. rewrite Epz2. apply (ext_sem_qdrain pz0 Hl0 ltac:(rewrite Zqn; clear - Hqn1; lia)).
      destruct Hbz as ((c & Hc & H1 & H2 & H3) & HB & HG). fold pz in H1, H2, HB, HG. unfold pz0. split; [|split].
      - exists c. split; [exact Hc|]. rewrite (qroom_sb pz sz Hlenz), (qroom_j pz sz Hlenz c (in_cls_rng c Hc)). split; [exact H1|]. split; [exact H2 | exact H3].
      - intros _. rewrite (qroom_sb pz sz Hlenz), (qroom_qj pz sz Hlenz). apply HB. clear - Hqn1. lia.
      - rewrite (qroom_sb pz sz Hlenz), (qroom_gn pz sz Hlenz), (qroom_gl pz sz Hlenz). exact HG. }
    (* [comment removed for export] *)
    assert (Hext_fr : forall b z, ext_sem (pden E a) b z -> forall x, b <= x < b + z -> hyb (wa x) = mem0 (wa x)).
    { intros b z Hbz x Hxr. destruct (ext_sem_pt pz mem0 HI b z x Hbz Hxr) as (Rx & Hap & _ & HnQ & HnG).
      apply (Hhyb_out x ltac:(clear - Rx; lia)). intros Hn.
      destruct Hn as [[Hn|Hn]|[Hn|(Hg1 & Hn)]].
      - exact (proj1 (proj2 (proj2 (cb_fp pz mem0 HI Hdisj x ltac:(clear - Hn; lia)))) Hap).
      - exact (HnQ ltac:(clear - Hqn1; lia) ltac:(unfold BQ in Hn; clear - Hn; lia)).
      - exact (proj1 (proj2 (proj2 (gq_fp pz mem0 HI x Hn))) Hap).
      - exact (HnG Hg1 ltac:(unfold BG in Hn; clear - Hn; lia)). }
    pose proof (HA_pri_step (s_next Lb) E E' M a mem0 hyb pri' HA0 HawLb Ha' Hne Hne' Hown_eq
                  ltac:(change (a_with a pri') with a'; rewrite Epz2; exact HIz') Hbase Hmono Hdepf Hext_step Hext_fr) as HA'.
    pose proof (own_pt_with (s_next Lb) E E' M a mem0 hyb pri' HA0 HawLb Ha' Hne Hown_eq
                  ltac:(change (a_with a pri') with a'; rewrite Epz2; exact HIz') Hbase Hmono) as Hsub.
    change (a_with a pri') with a' in HA', Hsub.
    (* [comment removed for export] *)
    set (Y := with_rgs X l'') in *.
    assert (HD8 : DEN ASEGS LIMIT model0 hyb E' Y (with_own M (a_own a')) ms' model').
    { apply (den_own_set ASEGS LIMIT model0 hyb hyb E' Y M ms' model' (a_own a') HD5).
      - apply forallb_forall. intros p Hp. rewrite forallb_forall in Cwo. specialize (Cwo p Hp). apply andb_prop in Cwo as [W1' W2'].
        apply andb_true_intro. split; apply (lwf_mono' (s_next S)); first [assumption | cbn [Y with_rgs X with_reg mrg Lh hand_post Lb nq_front s_next]; lia].
      - intros w _. reflexivity.
      - intros w Hw. apply Hsub. exact (proj1 (own_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw).
      - intros w (q & Hq & Hqw). cbn [with_own sm_own] in Hq.
        assert (Hw0 : own_pt E M w).
        { rewrite (ha_aown _ _ _ _ HA') in Hq. unfold aown_of in Hq. apply in_app_or in Hq as [Hq|Hq].
          * exists q. split.
            + rewrite Hown_eq, (ha_aown _ _ _ _ HA0). unfold aown_of. apply in_or_app. left. exact Hq.
            + assert (Hpw : pwf (s_next Lb) q = true).
              { pose proof HawLb as XW. unfold awf in XW. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [_ XW].
                rewrite forallb_forall in XW. apply XW. rewrite (ha_aown _ _ _ _ HA0). unfold aown_of. apply in_or_app. left. exact Hq. }
              unfold pwf in Hpw. apply andb_prop in Hpw as [Hp1 Hp2]. rewrite <- (uE_agree _ E E' _ Hp1 Ha'), <- (uE_agree _ E E' _ Hp2 Ha'). exact Hqw.
          * assert (Hq' : In q (pri_own a')) by (change (a_pri a') with pri' in Hq; destruct pri'; [destruct Hq | exact Hq]).
            pose proof (pri_own_foot E' a' hyb ltac:(unfold INV_A; rewrite Epz2; exact HIz') q Hq' w Hqw) as Hf.
            unfold pri_foot in Hf. rewrite Epz2 in Hf. apply Hfoot_eq in Hf.
            apply (po_own _ _ _ _ HP0 w); [pose proof (pri_foot_rng E a mem0 HI w Hf) as Pr; clear - Pr; lia | exact Hf]. }
        pose proof (proj2 (own_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw0) as (q0 & Hq0 & Hq0w).
        exact (dn_own _ _ _ _ _ _ _ _ _ HD5 q0 Hq0 w Hq0w). }
    apply (Hk E' hyb ms' model').
    + apply (agree_mono _ (s_next Lb)); [cbn [Lb nq_front s_next]; lia | exact Ha'].
    + intros q Hq w Hw. apply Hfrzn. exists q. split; [exact Hq | exact Hw].
    + exact HD8.
    + intros _. exact HA'.
Qed.
End NEnqDrain.
(* [comment removed for export] *)
End AcNEnqD.

Module AcNEnqD2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim StoreOk ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChFix FxChEnt FxWvC FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_put AXG_put3 AXG_np AXG_nf1 AXG_npf AXG_gp AXG_gf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_q3e.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require NqTail.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_npf OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gf1 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AXG_gpf OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q3.AXG_q2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q3.AXG_q1e OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q3e OSSVerify.Proofs.fast_float.from_chars.lib.AACB.NqTail.AXG_qt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarve AcSteps AcEntry AcMALp AcHand AcUnwApp0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDepDen AcAst AcHA AcFacts AcCarveP AcMALlib AcPutN AcUnwApp AcTbl.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConv AcConvG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep AcPriHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarveP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcOwnSet AcDenW AcConvA AcNPop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcNPopN AcNEnq.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcPutAppG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcShapes OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarveP OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPutN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcTblOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConv OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcRdw OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcPriDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarveP.AcStepsOut OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.AcAddOwn OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcOwnSet OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AcNPopApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AcRunApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNEnq.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import NqStepZ NqTail AcNEnqLib.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.



Section NEnqDrain2.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.

(* [comment removed for export] *)
Hypothesis batch_outside : forall mem0 E S M ms model a m0 jP jT, DEN ASEGS LIMIT model0 mem0 E S M ms model -> PRI_on E M a m0 ->
  find_grant (sm_maps M) (p_pg a) PG_SIZE = Some jP -> find_grant (sm_maps M) (p_tg a) TG_SIZE = Some jT ->
  forallb_l (fun R => pri_sep_c (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a R &&& batch_sep (s_facts S) a R) (s_rgs S) = true ->
  1 <= z_qn (pden E a) ->
  forall x, 0 <= x < two64 -> BQ (pden E a) <= x < BQ (pden E a) + 8192 -> outside E (s_rgs S) (Z_to_bv 64 x).

(* [comment removed for export] *)
Hypothesis gbatch_outside : forall mem0 E S M ms model a m0 jP jT, DEN ASEGS LIMIT model0 mem0 E S M ms model -> PRI_on E M a m0 ->
  find_grant (sm_maps M) (p_pg a) PG_SIZE = Some jP -> find_grant (sm_maps M) (p_tg a) TG_SIZE = Some jT ->
  forallb_l (fun R => pri_sep_c (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a R &&& batch_sep_at (s_facts S) a (p_gl a) R) (s_rgs S) = true ->
  1 <= z_gn (pden E a) ->
  forall x, 0 <= x < two64 -> BG (pden E a) <= x < BG (pden E a) + 8192 -> outside E (s_rgs S) (Z_to_bv 64 x).

#[using="Hwx gbatch_outside"] Theorem nenq_node_new_drain : forall S M a S' M' a', apost_nenq0 LIMIT S M a = Some (S', M', a') ->
  nq_room S a = false -> nq_nodrain S a = false ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx gbatch_outside : LiaFast.U) => LiaFast.u0).
  intros S M a S' M' a' H Hroom Hnd mem0 E ms model T Hd Haw HHA Hk.
  unfold nq_nodrain in Hnd. rewrite Hroom in Hnd. unfold nq_room in Hroom.
  unfold apost_nenq0 in H. cbv zeta in H. rewrite Hroom in H. rewrite Hnd in H.
  apply obool_some in H as (Hon & H).
  apply obind_some in H as (stk & Hstk & H). cbv beta in H.
  apply obind_some in H as (ro & Hro & H). cbv beta in H.
  apply obind_some in H as (ist & Hist & H). cbv beta in H.
  apply obind_some in H as (R & HR & H). cbv beta in H.
  apply obind_some in H as (o & Ho & H). cbv beta in H.
  apply obind_some in H as (cv & Hcv & H). cbv beta in H.
  apply obind_some in H as (jP & HjP & H). cbv beta in H.
  apply obind_some in H as (jT & HjT & H). cbv beta in H.
  apply obind_some in H as (gP & HgP & H). cbv beta in H.
  apply obool_some in H as (Hchk & H).
  apply obind_some in H as (l'' & Hsteps & H). cbv beta in H. injection H as <- <- <-.
  apply andb_prop in Hon as [Hon Hown_eq]. apply andb_prop in Hon as [Hon Hrs]. apply andb_prop in Hon as [Hon Hpc]. apply andb_prop in Hon as [Hon Hlen].
  apply Z.eqb_eq in Hpc. apply rsv_none_b_sound in Hrs. apply Nat.eqb_eq in Hlen.
  apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hown_eq.
  apply andb_prop in Hchk as [Hchk _]. apply andb_prop in Hchk as [Hchk Csep]. apply andb_prop in Hchk as [Hchk Cwo].
  apply andb_prop in Hchk as [Hchk Cwp]. apply andb_prop in Hchk as [Hchk CpX]. apply andb_prop in Hchk as [Hchk CwL].
  apply andb_prop in Hchk as [Hchk Cband]. apply andb_prop in Hchk as [Hchk Cge]. apply andb_prop in Hchk as [Hchk Cdr].
  apply andb_prop in Hchk as [Hchk Csz40]. apply andb_prop in Hchk as [Hchk Cs6]. apply andb_prop in Hchk as [Hchk Ccase]. apply andb_prop in Hchk as [Hchk Csbw].
  apply andb_prop in Hchk as [Hchk Cst]. apply andb_prop in Hchk as [Hchk Cro]. apply andb_prop in Hchk as [Hchk Cwin].
  apply andb_prop in Hchk as [Hchk Csphi]. apply andb_prop in Hchk as [Hchk Csplo]. apply andb_prop in Hchk as [Hchk Cmod].
  apply andb_prop in Hchk as [Hchk Cra]. apply andb_prop in Hchk as [Hchk Cs1]. apply andb_prop in Hchk as [Hchk Ca1].
  apply andb_prop in Hchk as [Cperm Ca0].
  apply andb_prop in Ccase as [Ccase Cjb]. apply andb_prop in Ccase as [Cqn0 Cqb0].
  apply andb_prop in Cdr as [Cdr Cj1]. apply andb_prop in Cdr as [Cdr Cgnhi]. apply andb_prop in Cdr as [Cdr Cgn]. apply andb_prop in Cdr as [Cdr Cmx].
  apply andb_prop in Cdr as [Cdr Cfrm]. apply andb_prop in Cdr as [Cdrlo Cs0].
  apply lin_eqb_eq in Ca0, Ca1, Cs1, Cra, Cs0. apply Z.leb_le in Csplo, Csphi, Cs6, Csz40, Cjb, Cdrlo, Cgnhi. apply Z.eqb_eq in Cqn0, Cqb0. apply Z.ltb_lt in Cj1.
  set (SPl := rget (s_regs S) (rk 2)) in *. set (szl := rget (s_regs S) (rk 14)) in *. set (s6l := rget (s_regs S) (rk 22)) in *.
  set (front := firstn 3 (carve_rgs cv)) in *. set (rest := skipn 3 (carve_rgs cv)) in *.
  set (L := nq_front S (s_next S) front) in *. set (Sp := nq_rest S rest) in *.
  set (Lb := nq_front S (s_next S + 66) front) in *.
  pose proof (HHA Hon) as HA0.
  assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hlen; discriminate).
  pose proof (ha_pri _ _ _ _ HA0 Hne) as HP0.
  (* [comment removed for export] *)
  pose proof (den_carve ASEGS LIMIT model0 mem0 E S M ms model _ _ _ cv Hd Hcv Cperm) as Hd1.
  assert (EQ1 : with_rgs S (carve_rgs cv) = mrg L Sp).
  { destruct S as [pc0 rg0 rgs0 fs0 nx0 rv0]. cbn [s_pc s_resv] in Hpc, Hrs. subst pc0 rv0.
    unfold with_rgs, mrg, L, Sp, nq_front, nq_rest. cbn [s_pc s_regs s_rgs s_facts s_next s_resv]. unfold front, rest. rewrite firstn_skipn. reflexivity. }
  rewrite EQ1 in Hd1.
  assert (EQb : bump (mrg L Sp) (s_next S + 66) = mrg Lb Sp) by reflexivity.
  pose proof (den_bump ASEGS LIMIT model0 mem0 E _ M ms model (s_next S + 66)%positive Hd1 ltac:(cbn [mrg s_next L nq_front]; lia)) as Hd2.
  rewrite EQb in Hd2.
  (* [comment removed for export] *)
  pose proof (po_inv _ _ _ _ HP0) as HI. unfold INV_A in HI. set (pz := pden E a) in *.
  pose proof (tg_pg_disj LIMIT model0 mem0 E S M ms model a mem0 Hd HP0) as Hdisj. fold pz in Hdisj.
  pose proof (az_geo pz mem0 HI) as G. destruct (q_seps pz mem0 HI Hdisj) as (T1 & S1 & S2 & B0).
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HRG & _ & HF0 & _).
  assert (Eqn : uE E (p_qn a) = z_qn pz) by (symmetry; apply zn_pden).
  assert (Eqb : uE E (p_qb a) = z_qb pz) by (symmetry; apply zn_pden).
  assert (Eca : uE E (p_ca a) = z_ca pz) by (symmetry; apply zn_pden).
  assert (Esb : uE E (p_sb a) = z_sb pz) by (symmetry; apply zn_pden).
  assert (Ej : uE E (p_j a 24) = z_j pz 24) by (symmetry; apply zn_pden).
  pose proof (irange_sound E (s_facts S) (p_qn a) HF0) as Rqn. fold (uE E (p_qn a)) in Rqn. rewrite Eqn in Rqn.
  pose proof (irange_sound E (s_facts S) (p_j a QCLS) HF0) as Rj. fold (uE E (p_j a QCLS)) in Rj. unfold QCLS in Rj, Cjb, Cj1. rewrite Ej in Rj.
  assert (Hj1 : 1 <= z_j pz 24) by (clear - Rj Cj1; lia).
  pose proof (irange_sound E (s_facts S) szl HF0) as Rsz. fold (uE E szl) in Rsz.
  pose proof (irange_sound E (s_facts S) s6l HF0) as Rs6. fold (uE E s6l) in Rs6.
  pose proof (irange_sound E (s_facts S) SPl HF0) as Rsp. fold (uE E SPl) in Rsp.
  assert (Hal : uE E SPl mod 16 = 0) by (pose proof (fact_implied_ok E _ _ HF0 Cmod) as X; cbn [fact_ok] in X; exact X).
  destruct (iz_q _ _ HI) as [HQ0 _].
  (* [comment removed for export] *)
  assert (Rqf : fst (irange (s_facts S) (laddc szl 8192)) <= uE E szl + 8192 <= snd (irange (s_facts S) (laddc szl 8192))).
  { pose proof (irange_sound E (s_facts S) (laddc szl 8192) HF0) as X. fold (uE E (laddc szl 8192)) in X.
    assert (Y : snd (irange (s_facts S) szl) <= 2^40) by (first [exact Csz40 | apply Z.leb_le; exact Csz40]).
    rewrite uE_laddc_z in X by (pose proof (uE_range E szl) as U; clear - U Y Rsz; unfold two64 in *; lia). exact X. }
  cbv iota in Cdrlo.
  assert (Hqn0 : z_qn pz = 0 /\ z_qb pz = 0).
  { destruct HQ0 as (_ & _ & [(Q0 & Q1 & _)|(Q1 & _)]); [split; assumption | clear - Q1 Rqn Cqn0; lia]. }
  destruct Hqn0 as [Hqn0 Hqb0].
  assert (Hjhi : z_j pz 24 + 1 + mc_tbl 24 / 2 <= 262144 / sz_tbl 24) by (clear - Rj Cjb; lia).
  assert (Hj32 : z_j pz 24 + 2 <= 32) by (revert Hjhi; change (262144 / sz_tbl 24) with 32; change (mc_tbl 24 / 2) with 1; clear; lia).
  destruct (iz_cls _ _ HI 24 in_cls_24) as [(J0 & _)|(_ & Z1 & Jb & HIo & HPo)]; [clear - J0 Hj1; lia|].
  pose proof (iz_st _ _ HI) as HST.
  change (sz_tbl 24) with 8192 in HIo, HPo. change (mc_tbl 24 / 2) with 1 in HIo. change (262144 / 8192) with 32 in HIo.
  assert (Egn : uE E (p_gn a) = z_gn pz) by (symmetry; apply zn_pden).
  assert (Egb : uE E (p_gb a) = z_gb pz) by (symmetry; apply zn_pden).
  pose proof (irange_sound E (s_facts S) (p_gn a) HF0) as Rgn. fold (uE E (p_gn a)) in Rgn. rewrite Egn in Rgn.
  pose proof (irange_sound E (s_facts S) (p_gb a) HF0) as Rgb. fold (uE E (p_gb a)) in Rgb. rewrite Egb in Rgb.
  destruct (iz_gq _ _ HI) as [HG0 HGl].
  assert (Hgn0 : 0 <= z_gn pz /\ 0 <= z_gb pz < 2^62) by (destruct HG0 as (X1 & X2 & _); clear - X1 X2; lia).
  assert (Hgl0 : 1 <= z_gn pz -> 0 <= z_gl pz < 32).
  { intros Hg1. destruct HG0 as (_ & _ & _ & _ & _ & _ & _ & _ & [(X0 & _)|(_ & X1 & _)]); [clear - X0 Hg1; lia | exact X1]. }
  (* [comment removed for export] *)
  destruct (rdw IMGP (s_rgs S) (lconst 930608) 8) as [mxl|] eqn:Wmx; [|discriminate].
  destruct (is_const mxl) as [mxs|] eqn:Emx; [|discriminate]. apply andb_prop in Cmx as [Cmx1 Cmx2]. apply Z.leb_le in Cmx1. apply Z.ltb_lt in Cmx2.
  cbv iota in Cmx1.
  destruct (is_const (rg_size R)) as [zz|] eqn:Ezz; [|discriminate]. apply Z.leb_le in Cfrm.
  (* [comment removed for export] *)
  destruct (rg_hdr_b_sound _ _ _ _ Cwin) as (cw & Pw). destruct (ro_b_sound _ Cro) as (zro & Hzro & Pro).
  destruct (rg_hdr_b_sound _ _ _ _ Cst) as (cs & Pst).
  assert (HwLb : state_wf Lb = true) by (apply (nq_front_wf_mono S (s_next S) (s_next S + 66)%positive front ltac:(lia) CwL)).
  (* [comment removed for export] *)
  unfold sb_words_ok in Csbw. destruct (rdw IMGP (s_rgs S) (lconst 929848) 8) as [l1|] eqn:W1; [|discriminate].
  destruct (rdw IMGP (s_rgs S) (lconst 929864) 8) as [l2|] eqn:W2; [|discriminate].
  apply andb_prop in Csbw as [Q1 Q2]. apply lin_eqb_eq in Q1, Q2. subst l1 l2.
  pose proof (rdw_sound IMGP IMGP_ok E _ (s_rgs S) (lconst 929848) 8 _ HRG ltac:(lia) W1) as RSB.
  pose proof (rdw_sound IMGP IMGP_ok E _ (s_rgs S) (lconst 929864) 8 _ HRG ltac:(lia) W2) as RRIB.
  rewrite uE_lc in RSB, RRIB by lia. rewrite Esb in RSB.
  assert (Erip : uE E (l_rip a) = z_sb pz + 137438953472).
  { unfold l_rip. rewrite uE_laddc2 by (rewrite ?Esb; unfold two64; clear - G; lia). rewrite Esb. reflexivity. }
  rewrite Erip in RRIB.
  pose proof (rdw_sound IMGP IMGP_ok E _ (s_rgs S) (lconst 930608) 8 _ HRG ltac:(lia) Wmx) as RMX.
  rewrite uE_lc in RMX by lia. unfold uE in RMX. rewrite (is_const_u E mxl mxs Emx) in RMX.
  (* [comment removed for export] *)
  destruct (po_gp _ _ _ _ HP0) as (kp & Hgp). destruct (po_gt _ _ _ _ HP0) as (kt & Hgt).
  pose proof (band_hi LIMIT model0 mem0 E S M ms model SPl _ Hd Cband Hgp) as BP.
  pose proof (band_hi LIMIT model0 mem0 E S M ms model SPl _ Hd Cband Hgt) as BT.
  unfold gsz in BP, BT. cbn [fst snd] in BP, BT. unfold PG_SIZE, TG_SIZE in BP, BT. rewrite uE_lc in BP, BT by lia.
  assert (Epg : uE E (p_pg a) = z_pg pz) by (symmetry; apply zn_pden).
  assert (Etg : uE E (p_tg a) = z_tg pz) by (symmetry; apply zn_pden).
  rewrite Epg in BP. rewrite Etg in BT. fold (uE E SPl) in BP, BT.
  (* [comment removed for export] *)
  destruct (forallb_l_and3' _ _ _ _ Csep) as [Csep_b Csep_g]. pose proof (forallb_l_and1 _ _ _ Csep_b) as Csep'.
  assert (Hjn : z_j pz 24 + 1 <= 262144 / sz_tbl 24) by (change (262144 / sz_tbl 24) with 32; clear - Hj32; lia).
  assert (HCELLn : forall x, 0 <= x < 2^64 -> qncell pz x -> own_pt E M x /\ outside E (s_rgs (mrg Lb Sp)) (wa x) /\ ~ frz_pt E M x).
  { intros x Hx Hq.
    assert (F : pri_foot_z pz x /\ FPmax pz x /\ ~ alloc_part pz x).
    { destruct Hq as [Hq|[Hq|Hq]].
      - destruct (ncell_fp pz mem0 HI Hdisj 24 x in_cls_24 Z1 Hq) as (F1 & F2 & F3 & _). split; [exact F1|]. split; [exact F2 | exact F3].
      - destruct (cb_fp pz mem0 HI Hdisj x ltac:(clear - Hq; lia)) as (F1 & F2 & F3 & _). split; [exact F1|]. split; [exact F2 | exact F3].
      - destruct (chunk_fp pz mem0 HI 24 x in_cls_24 Z1 Hjn ltac:(change (sz_tbl 24) with 8192; unfold BN in Hq; clear - Hq; lia)) as (F1 & F2 & F3 & _).
        split; [exact F1|]. split; [exact F2 | exact F3]. }
    destruct F as (F1 & F2 & F3).
    split; [exact (po_own _ _ _ _ HP0 x Hx F1)|]. split.
    - exact (pri_outside_den LIMIT model0 mem0 E (mrg L Sp) M ms model a mem0 jP jT Hd1 HP0 HjP HjT Csep' x ltac:(unfold two64; lia) F2 F3).
    - exact (pri_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1). }
  assert (HCELL : forall x, 0 <= x < 2^64 -> qndcell pz x -> own_pt E M x /\ outside E (s_rgs (mrg Lb Sp)) (wa x) /\ ~ frz_pt E M x).
  { intros x Hx [Hq|[Hq|(Hg1 & Hq)]]; [exact (HCELLn x Hx Hq) | |].
    - destruct (gq_fp pz mem0 HI x Hq) as (F1 & F2 & F3 & F4).
      split; [exact (po_own _ _ _ _ HP0 x Hx F1)|]. split.
      + exact (pri_outside_den LIMIT model0 mem0 E (mrg L Sp) M ms model a mem0 jP jT Hd1 HP0 HjP HjT Csep' x ltac:(unfold two64; lia) F2 F3).
      + exact (pri_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1).
    - destruct (bg_fp pz mem0 HI Hg1 x ltac:(clear - Hq; lia)) as (F1 & F2 & F4).
      split; [exact (po_own _ _ _ _ HP0 x Hx F1)|]. split.
      + destruct (Z.eqb (snd (irange (s_facts S) (p_gn a))) 0) eqn:Egn0; [apply Z.eqb_eq in Egn0; exfalso; clear - Egn0 Rgn Hg1; lia|].
        cbv iota in Csep_g.
        exact (gbatch_outside mem0 E (mrg L Sp) M ms model a mem0 jP jT Hd1 HP0 HjP HjT Csep_g ltac:(fold pz; exact Hg1) x ltac:(unfold two64; lia) ltac:(fold pz; clear - Hq; lia)).
      + exact (pri_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1). }
  (* [comment removed for export] *)
  pose proof (dn_sden _ _ _ _ _ _ _ _ _ Hd2) as Hsd. pose proof (dn_own _ _ _ _ _ _ _ _ _ Hd2) as Hown.
  set (H := Hof E M model) in *. set (msr := restrict H ms) in *.
  pose proof (sden_0 _ _ _ _ Hsd) as Hd0.
  assert (Hsvc : ms_svc_pending ms = None) by (destruct Hd0 as (_ & X & _); exact X).
  assert (Hrv : ms_resv ms = None).
  { destruct Hd0 as (_ & _ & X & _). cbn [mrg s_resv Lb nq_front] in X. cbn [rsv_ok] in X. exact X. }
  set (SP := uE E SPl) in *. set (CA := z_ca pz) in *. set (QC := CA - 128) in *. set (SB := z_sb pz) in *. set (j := z_j pz 24) in *.
  assert (Ecb : uE E (l_cb a) = QC).
  { unfold l_cb. rewrite uE_laddc_z by (rewrite Eca; unfold two64; clear - B0; fold CA in B0; lia). rewrite Eca. reflexivity. }
  assert (R1 : getr (ms_regs ms) (Z_to_bv 5 1) = wa 278036).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 1) _ Hd0 Cra). rewrite lden_lconst. reflexivity. }
  assert (R2 : getr (ms_regs ms) (Z_to_bv 5 2) = wa SP).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 2) _ Hd0 eq_refl). unfold wa, SP, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R8 : getr (ms_regs ms) (Z_to_bv 5 8) = wa 930544).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 8) _ Hd0 Cs0). rewrite lden_lconst. reflexivity. }
  assert (R9 : getr (ms_regs ms) (Z_to_bv 5 9) = wa QC).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 9) _ Hd0 Cs1). rewrite <- Ecb. unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = wa QC).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 10) _ Hd0 Ca0). rewrite <- Ecb. unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R11 : getr (ms_regs ms) (Z_to_bv 5 11) = wa CA).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 11) _ Hd0 Ca1). rewrite <- Eca. unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R14 : getr (ms_regs ms) (Z_to_bv 5 14) = wa (uE E szl)).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 14) _ Hd0 eq_refl). unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R22 : getr (ms_regs ms) (Z_to_bv 5 22) = wa (uE E s6l)).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 22) _ Hd0 eq_refl). unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  (* [comment removed for export] *)
  pose proof (mrg_rg0 E Lb Sp msr 0%nat _ Hd0 Pw) as Rw. pose proof (mrg_rg0 E Lb Sp msr 1%nat _ Hd0 Pro) as Rro.
  assert (HSPr : 2^46 + 8192 <= SP <= 2^47) by (clear - Rsp Csplo Csphi; unfold SP; lia).
  assert (Ebw : bv_unsigned (lden E (laddc SPl (-2064))) = SP - 2064) by (rewrite lden_laddc; fold (uE E SPl); fold SP; rewrite u_small64; unfold two64; clear - HSPr; lia).
  assert (Bw : forall x, SP - 2064 <= x < SP -> rd1 ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None /\ wview ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None).
  { intros x Hx. apply (rg_rw_pt _ _ _ x Rw eq_refl). cbn [rg_base]. rewrite Ebw. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; clear; lia). clear - Hx. lia. }
  assert (Hstko : stk_ok ASEGS (ms_mem msr) (wa SP) 2048).
  { intros a0 k Ha Hk'. rewrite u_wa_small in Ha, Hk' by (clear - HSPr; lia). apply store_ok_of_all; [pose proof (bv_unsigned_in_range _ a0) as Ra0; clear - Ra0 Ha Hk' HSPr; lia|].
    intros x Hx. pose proof (bv_unsigned_in_range _ x) as Rx. destruct (Bw (bv_unsigned x) ltac:(clear - Hx Ha Hk'; lia)) as [_ W]. rewrite Z_to_bv_bv_unsigned in W. exact W. }
  assert (Bro : forall i, 65536 <= i < 143360 -> ms_mem msr (Z_to_bv 64 i) = None) by exact (ro_none_z _ _ _ Hzro Rro).
  (* [comment removed for export] *)
  assert (Hcelld : forall x, 0 <= x < 2^64 -> qndcell pz x -> ms_mem msr (wa x) = mem0 (wa x) /\ H (wa x) = false).
  { intros x Hx Hc0. destruct (HCELL x Hx Hc0) as ((p & Hp & Hpw) & Hout & _). pose proof (Hown p Hp x Hpw) as [Hv Hm].
    fold H in Hv. unfold wa. split; [|exact Hv]. cbn [msr restrict ms_mem]. unfold mrestrict. rewrite Hv. apply Hm. exact Hout. }
  assert (Hcell : forall x, 0 <= x < 2^64 -> qncell pz x -> ms_mem msr (wa x) = mem0 (wa x) /\ H (wa x) = false) by (intros x Hx Hq; exact (Hcelld x Hx (or_introl Hq))).
  assert (B1 : 0 <= CA /\ CA + 4096 <= 2^63 /\ 0 <= SB /\ SB + 137438953472 + 4096 <= 2^63) by (unfold CA, SB; clear - B0; lia).
  assert (IQ : q_inv (ms_mem msr) QC SB (z_qj pz) 0 0).
  { rewrite <- Hqn0 at 1. rewrite <- Hqb0. apply (q_inv_frame mem0); [unfold QC; clear - B1 B0; fold CA in B0; lia | unfold QC; clear - B1; lia | clear - B1; lia | clear - B1; lia | | | exact HQ0].
    - intros x Hx. apply (Hcell x); [unfold QC in Hx; clear - Hx B0; fold CA in B0; lia | right; left; unfold QC in Hx; fold CA; clear - Hx; lia].
    - intros Hc0. exfalso. clear - Hc0 Hqn0. lia. }
  assert (HIor : INV_Co (ms_mem msr) CA SB 24 8192 1 32 j).
  { apply (INV_Co_frame mem0); [clear - B1; lia | clear - B1; lia | clear - B1; lia | clear - B1; lia | | exact HIo]. intros x Hf.
    assert (Hx : 0 <= x < 2^64) by (unfold foot_Co in Hf; clear - Hf B1; lia). exact (proj1 (Hcell x Hx (or_introl (or_introl Hf)))). }
  assert (HSTr : STATS (ms_mem msr) CA).
  { apply (STATS_frame mem0); [clear - B1; lia | clear - B1; lia | | exact HST]. intros x Hx. apply (Hcell x); [clear - Hx B1; lia | left; right; exact Hx]. }
  pose proof (INV_Co_G _ _ _ _ _ _ _ _ HIor) as HIG.
  assert (RSBr : rd (ms_mem msr) 929848 8 SB) by exact RSB.
  assert (RRIBr : rd (ms_mem msr) 929864 8 (SB + 137438953472)) by exact RRIB.
  specialize (HIG RSBr RRIBr HSTr).
  assert (Hwq : wr (ms_mem msr) QC 32).
  { apply (wr_frame mem0); [unfold QC; clear - B0; fold CA in B0; lia | unfold QC; clear - B1; lia | |].
    - intros x Hx. apply (Hcell x); [unfold QC in Hx; clear - Hx B0; fold CA in B0; lia | right; left; fold CA; unfold QC in Hx; clear - Hx; lia].
    - intros d k Hd' Hk'. replace (QC + d) with (z_ca pz - 128 + d) by (unfold QC, CA; ring). apply (iz_wc _ _ HI); lia. }
  assert (Hwb : wr (ms_mem msr) (SB + 103079215104 + 8192 * j) 8192).
  { apply wr_bytes; [clear - B1 Hj1; lia | clear - B1 Hj32; lia|]. intros x Hx.
    destruct (Hcell x ltac:(clear - Hx B1 Hj1 Hj32; lia) ltac:(right; right; unfold BN; fold SB; fold j; exact Hx)) as [Hm _].
    unfold wview. rewrite Hm. rewrite (pc_map _ _ _ _ _ _ HPo x ltac:(unfold RBX; fold SB; fold j; clear - Hx Hj32; lia)). discriminate. }
  set (mp := bv_unsigned (getr (ms_regs ms) (Z_to_bv 5 13))).
  set (sz := uE E szl) in *. set (mx := uE E s6l) in *.
  assert (Hnum : 0 <= sz <= 2^40 /\ 0 <= mp < 2^64 /\ 0 <= mx < 2^62 /\ mx + 1 <= sz + 8192 /\ sz + 8192 + z_gb pz <= mxs).
  { pose proof (uE_range E szl) as U1. pose proof (uE_range E s6l) as U2. pose proof (bv_unsigned_in_range _ (getr (ms_regs ms) (Z_to_bv 5 13))) as U3.
    pose proof (irange_sound E (s_facts S) (p_qb a) HF0) as Rqb. fold (uE E (p_qb a)) in Rqb. rewrite Eqb, Hqb0 in Rqb.
    fold mp in U3. fold sz in U1, Rsz. fold mx in U2, Rs6.
    clear - U1 U2 U3 Hgn0 Rqb Rgb Rsz Rs6 Cs6 Csz40 Cdrlo Cmx1 Cmx2 Rqf. unfold two64 in *. change (bv_modulus 64) with 18446744073709551616 in U3. lia. }
  assert (HCAf : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA mod 16 = 0 /\ CA + 2592 <= SP - 2048).
  { pose proof (iz_ca _ _ HI) as (X1 & X2 & X3). fold pz in X1, X2, X3. fold CA in X1, X2, X3. split; [exact X1|]. split; [exact X2|]. clear - G BT HSPr. fold CA in G. lia. }
  assert (HSBf : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048).
  { pose proof (iz_sb _ _ HI) as (X1 & X2). fold pz in X1, X2. fold SB in X1, X2. split; [exact X1|]. split; [exact X2 | clear - G BP B0; fold SB in G, B0; lia]. }
  assert (HSEPf : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= QC) by (unfold QC; clear - T1 B0; fold CA in T1, B0; fold SB in B0; lia).
  assert (HQCf : ((4176 <= QC /\ QC + 4016 <= 65536) \/ 6537296 <= QC) /\ QC + 32 <= SP - 2048) by (unfold QC; clear - HCAf; lia).
  assert (HSEPq : QC + 32 <= SB \/ SB + 137438953472 + 4096 <= QC) by (unfold QC; clear - HSEPf; lia).
  (* [comment removed for export] *)
  assert (Bf : forall x, SP <= x < SP + 16 -> rd1 ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None /\ wview ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None).
  { intros x Hx. rewrite Forall_forall in HRG. pose proof (HRG R (nth_error_In _ _ HR)) as RR.
    assert (HkR : rg_kind R = RW).
    { pose proof Hcv as X. unfold carve_of in X. rewrite HR in X. destruct R as [b0 z0 k0 c0]. destruct k0; try discriminate. reflexivity. }
    destruct (lin_off_sound E SPl (rg_base R) o Ho) as [_ Ho0].
    pose proof RR as Hrsz. destruct Hrsz as (_ & Hrsz & _). cbv zeta in Hrsz.
    assert (Ezr : rsz E R = zz) by (unfold rsz; exact (is_const_u E _ _ Ezz)).
    pose proof (FxChFix.lin_off_u E SPl (rg_base R) o Ho ltac:(rewrite Ezr in Hrsz; clear - Hrsz Cfrm Ho0; unfold two64 in *; lia)) as Eo. fold (uE E SPl) in Eo. fold SP in Eo.
    apply (rg_rw_pt _ _ _ x RR ltac:(rewrite HkR; reflexivity)). rewrite Ezr. clear - Hx Eo Cfrm Ho0. lia. }
  assert (IGQ : gq_inv (ms_mem msr) SB (z_gn pz) (z_gl pz) (z_gb pz) mxs).
  { apply gq_inv_of_o; [|clear - Hnum Hgn0 Cmx2; lia | exact RMX].
    apply (gq_inv_o_frame mem0); [clear - B1; lia | clear - B1; lia | | exact HG0].
    intros x [Hx|(Hg1 & Hx)]; apply (Hcelld x).
    - clear - Hx. lia.
    - right. left. exact Hx.
    - specialize (Hgl0 Hg1). clear - Hx B1 Hgl0. lia.
    - right. right. split; [exact Hg1 | unfold BG; exact Hx]. }
  (* [comment removed for export] *)
  destruct (@qnew_e (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_rom ms) (ms_mem msr) (ms_regs ms) QC CA SB 1 32 j (z_qj pz) sz mp mx SP IQ HIG
              ltac:(clear - Hj32; lia))
    as (Ra & m1 & Hms1 & HK1 & HQ1 & HIG1 & _ & _ & Hfr1 & Hgr1).
  all: try (replace (1%bv : reg) with (Z_to_bv 5 1) by (apply bv_eq; reflexivity); exact R1).
  all: try (replace (2%bv : reg) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity); exact R2).
  all: try (replace (9%bv : reg) with (Z_to_bv 5 9) by (apply bv_eq; reflexivity); exact R9).
  all: try (replace (10%bv : reg) with (Z_to_bv 5 10) by (apply bv_eq; reflexivity); exact R10).
  all: try (replace (11%bv : reg) with (Z_to_bv 5 11) by (apply bv_eq; reflexivity); exact R11).
  all: try (replace (13%bv : reg) with (Z_to_bv 5 13) by (apply bv_eq; reflexivity); unfold mp, wa; rewrite Z_to_bv_bv_unsigned; reflexivity).
  all: try (replace (14%bv : reg) with (Z_to_bv 5 14) by (apply bv_eq; reflexivity); exact R14).
  all: try (replace (22%bv : reg) with (Z_to_bv 5 22) by (apply bv_eq; reflexivity); exact R22).
  all: try exact Hstko. all: try exact Hwq. all: try exact Hwb. all: try exact Bro. all: try reflexivity.
  all: try exact HCAf. all: try exact HSBf. all: try exact HSEPf.
  all: try (split; [clear - HSPr; lia | exact Hal]).
  { clear - Hnum. lia. }
  (* [comment removed for export] *)
  set (B := SB + 103079215104 + 8192 * j) in *.
  assert (Hfr1' : forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> ~ owned_C CA SB 24 x -> ~ (QC <= x < QC + 32) -> ~ (B <= x < B + 8192) -> m1 (wa x) = ms_mem msr (wa x)).
  { intros x Hx N0 N1 N2 N3. apply Hfr1; [exact Hx | exact N0 | exact N1 | exact N2 | clear - N3; lia]. }
  assert (Hgqf : forall x, 930696 <= x < 930736 -> m1 (wa x) = ms_mem msr (wa x)).
  { intros x Hx. apply Hfr1'; [clear - Hx; lia | clear - Hx HSPr; lia | unfold owned_C; clear - Hx HCAf HSBf; lia | clear - Hx HQCf; lia | unfold B; clear - Hx HSBf Hj1; lia]. }
  assert (IGQ1 : gq_inv m1 SB (z_gn pz) (z_gl pz) (z_gb pz) mxs).
  { apply gq_inv_of_o; [|clear - Hnum Hgn0 Cmx2; lia |].
    - apply (gq_inv_o_frame (ms_mem msr)); [clear - B1; lia | clear - B1; lia | | exact (gq_inv_to_o _ _ _ _ _ _ IGQ)].
      intros x [Hx|(Hg1 & Hx)]; [exact (Hgqf x Hx)|]. specialize (Hgl0 Hg1). specialize (HGl Hg1). fold j in HGl.
      apply Hfr1'; [clear - Hx B1 Hgl0; lia | clear - Hx HSBf Hgl0; lia | unfold owned_C; clear - Hx HSEPf HCAf HSBf Hgl0 B1; lia | clear - Hx HSEPq HQCf Hgl0 B1; lia | unfold B; clear - Hx HGl; lia].
    - apply (rd_frame (ms_mem msr)); [lia | cbn; lia | | exact RMX]. intros x Hx. cbn in Hx.
      apply Hfr1'; [clear - Hx; lia | clear - Hx HSPr; lia | unfold owned_C; clear - Hx HCAf HSBf; lia | clear - Hx HQCf; lia | unfold B; clear - Hx HSBf Hj1; lia]. }
  assert (Hstk1 : stk_ok ASEGS m1 (wa SP) 2048) by exact (stk_ok_grows ASEGS _ _ _ _ Hstko Hgr1).
  assert (Hwq1 : wr m1 QC 32) by (intros d k Hd' Hk'; apply (store_ok_mono ASEGS k (ms_mem msr) m1 _ Hgr1); exact (Hwq d k Hd' Hk')).
  assert (Bf1 : forall x, SP <= x < SP + 16 -> rd1 ASEGS m1 (Z_to_bv 64 x) <> None).
  { intros x Hx. destruct (Bf x Hx) as [X1 X2]. exact (proj1 (grows_rw ASEGS (ms_mem msr) m1 _ Hgr1 X1 X2)). }
  destruct (rdn_some m1 SP 8 ltac:(clear - HSPr; lia) ltac:(cbn; unfold two64; clear - HSPr; lia)) as (bs2 & Hbs2).
  { intros i Hi. cbn in Hi. apply Bf1. clear - Hi. lia. }
  destruct (rd_exists m1 SP 8 bs2 ltac:(lia) Hbs2) as (pa2 & Hpa2a & Hpa2b & S0).
  destruct (rdn_some m1 (SP + 8) 8 ltac:(clear - HSPr; lia) ltac:(cbn; unfold two64; clear - HSPr; lia)) as (bs3 & Hbs3).
  { intros i Hi. cbn in Hi. apply Bf1. clear - Hi. lia. }
  destruct (rd_exists m1 (SP + 8) 8 bs3 ltac:(lia) Hbs3) as (pa3 & Hpa3a & Hpa3b & S8).
  (* [comment removed for export] *)
  destruct (@qtail_d (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_rom ms) m1 Ra QC SB j 1 (sz + 8192) mx (z_gn pz) (z_gl pz) (z_gb pz) mxs SP pa2 pa3
              HQ1 ltac:(lia) IGQ1 ltac:(clear - Rgn Cgnhi; lia))
    as (Rb & m2 & Hms2 & HRb1 & HK2 & HQ2 & HG2 & Hfr2 & Hgr2).
  1: { replace (2%bv : reg) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). rewrite (HK1 2%nat ltac:(clear; unfold KQC; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])). exact R2. }
  1: { replace (8%bv : reg) with (Z_to_bv 5 (Z.of_nat 8)) by (apply bv_eq; reflexivity). rewrite (HK1 8%nat ltac:(clear; unfold KQC; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])). exact R8. }
  1: { replace (9%bv : reg) with (Z_to_bv 5 (Z.of_nat 9)) by (apply bv_eq; reflexivity). rewrite (HK1 9%nat ltac:(clear; unfold KQC; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])). exact R9. }
  1: { replace (22%bv : reg) with (Z_to_bv 5 (Z.of_nat 22)) by (apply bv_eq; reflexivity). rewrite (HK1 22%nat ltac:(clear; unfold KQC; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])). exact R22. }
  2: exact Hstk1. 2: exact S0. 2: exact S8. 3: exact HQCf. 3: exact HSBf. 3: exact HSEPq. 4: exact Hwq1.
  { clear - HSPr. lia. }
  { clear - Hpa2a Hpa2b Hpa3a Hpa3b. lia. }
  { clear - Hnum. lia. }
  (* [comment removed for export] *)
  pose proof (msteps_trans ASEGS _ _ _ Hms1 Hms2) as Hms.
  assert (Hgr : mem_grows (ms_mem msr) m2) by exact (mem_grows_trans _ _ _ Hgr1 Hgr2).
  assert (Hpc0 : ms_pc_val ms = wa 0x43e20) by (destruct Hd0 as (X & _); cbn [mrg s_pc Lb nq_front] in X; exact X).
  rewrite <- Hpc0 in Hms.
  assert (Est : uE E (laddc (p_tg a) 2872) = z_tg pz + 2872).
  { rewrite uE_laddc_z by (rewrite Etg; unfold two64; clear - G; lia). rewrite Etg. reflexivity. }
  assert (Hfr2' : forall x, 0 <= x < 2^64 -> ~ (SP - 2064 <= x < SP) -> ~ qndcell pz x -> m2 (wa x) = m1 (wa x)).
  { intros x Hx N0 Nq. apply Hfr2; [exact Hx | clear - N0; lia | | |].
    - intros Hc0. apply Nq. left. right. left. fold CA. unfold QC in Hc0. clear - Hc0. lia.
    - intros Hc0. apply Nq. right. left. exact Hc0.
    - intros (Hg1 & Hc0). apply Nq. right. right. split; [exact Hg1 | unfold BG; fold SB; exact Hc0]. }
  assert (Hfr1q : forall x, 0 <= x < 2^64 -> ~ (SP - 2064 <= x < SP) -> ~ qndcell pz x -> m1 (wa x) = ms_mem msr (wa x)).
  { intros x Hx N0 Nq. apply Hfr1'; [exact Hx | clear - N0; lia | | |].
    - intros Hc0. apply Nq. left. left. unfold owned_C in Hc0. unfold ncell, foot_Co. fold CA. fold SB. clear - Hc0. lia.
    - intros Hc0. apply Nq. left. right. left. fold CA. unfold QC in Hc0. clear - Hc0. lia.
    - intros Hc0. apply Nq. left. right. right. unfold BN. fold SB. fold j. exact Hc0. }
  assert (HKb : forall k, In k [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat -> getr Rb (Z_to_bv 5 (Z.of_nat k)) = getr (ms_regs ms) (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk'. rewrite (HK2 k Hk'). apply HK1. clear - Hk'. unfold KQC. cbn [In] in *. intuition. }
  apply (den_run_app cfg LIMIT model0 Hwx mem0 Lb Sp E M ms model T SPl (laddc (p_tg a) 2872) 0%nat 2%nat cw cs 0x43d4c KT2k
           [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat Rb m2 (qndcell pz) 2064 ltac:(lia) Hd2 HwLb eq_refl Pw Pst).
  - fold SP. clear - HSPr. lia.
  - rewrite Est. clear - G BT HSPr. fold SP in BT. lia.
  - exact kt2_cases.
  - exact Hms.
  - exact HKb.
  - exact HCELL.
  - intros x Hx Hw _ Hq. fold SP in Hw. rewrite (Hfr2' x Hx Hw Hq). exact (Hfr1q x Hx Hw Hq).
  - exact Hgr.
  - intros E' ms' model' HD' Ha' Hfz' Hrr Hvis.
    set (Lh := hand_post Lb 0x43d4c KT2k [0%nat; 2%nat]) in *.
    set (hyb := hyb_p (qndcell_b pz) (ms_mem ms') mem0).
    assert (HwfM : sm_wf (s_next Lb) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd2).
    assert (HbwS : bases_wf (s_next Lb) (s_rgs (mrg Lb Sp)) = true) by exact (dn_bases _ _ _ _ _ _ _ _ _ Hd2).
    assert (Hsh : shape (s_rgs (mrg Lh Sp)) = shape (s_rgs (mrg Lb Sp))).
    { cbn [mrg s_rgs]. unfold Lh, hand_post. cbn [s_rgs]. unfold shape. rewrite !map_app. f_equal.
      pose proof (empty_at_shape [0%nat; 2%nat] (s_rgs Lb) 0) as Hs. unfold shape in Hs. exact Hs. }
    assert (Hnwin : forall w, outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w) -> 0 <= w < two64 -> ~ (SP - 2064 <= w < SP)).
    { intros w Hout Hw Hc0. unfold outside in Hout. rewrite Forall_forall in Hout. cbn [mrg s_rgs] in Hout.
      specialize (Hout _ ltac:(apply in_or_app; left; exact (nth_error_In _ _ Pw))). cbn [rg_base] in Hout.
      unfold rsz in Hout. cbn [rg_size] in Hout. rewrite lden_lconst, (u_small64 2064) in Hout by (unfold two64; clear; lia).
      rewrite Ebw in Hout. rewrite u_small64 in Hout by exact Hw. clear - Hout Hc0. lia. }
    assert (Hkeep : forall w, 0 <= w < two64 -> own_pt E M w -> outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w) ->
              ~ qndcell pz w -> ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
    { intros w Hw (q & Hq & Hqw) Hout Hnc. destruct (Hown q Hq w Hqw) as [Hv Hm]. rewrite <- (Hm Hout). fold H in Hv.
      rewrite (Hvis _ Hv). change (Z_to_bv 64 w) with (wa w).
      rewrite (Hfr2' w ltac:(unfold two64 in Hw; exact Hw) (Hnwin w Hout Hw) Hnc), (Hfr1q w ltac:(unfold two64 in Hw; exact Hw) (Hnwin w Hout Hw) Hnc).
      cbn [msr restrict ms_mem]. unfold mrestrict, wa. rewrite Hv. reflexivity. }
    assert (Hfrzn : forall w, frz_pt E M w -> hyb (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
    { intros w Hw. unfold hyb, hyb_p. destruct (qndcell_b _ _); [exact (Hfz' w Hw) | reflexivity]. }
    assert (Hw64 : forall w, own_pt E M w -> 0 <= w < two64).
    { intros w Hw0. destruct (Z_lt_le_dec w two64) as [X|X].
      - destruct Hw0 as (q & Hq & Hqw). pose proof (uE_range E (fst q)) as Uq. clear - Uq Hqw X. lia.
      - exfalso. destruct (ha_ownx _ _ _ _ HA0 w (own_pt_a_M E M a w Hown_eq Hw0)) as [Dc|[_ Pf]].
        + destruct HA0 as [(n0 & F0 & st0 & I0 & _) _ _ _ _ _ _]. destruct I0 as [_ _ _ D1r _ _ _ _ _ B1r _ _ _].
          unfold dcov in Dc. unfold two64 in X. clear - Dc X D1r B1r. lia.
        + pose proof (pri_foot_rng E a mem0 HI w Pf) as Pr. unfold two64 in X. clear - Pr X. lia. }
    assert (HD3 : DEN ASEGS LIMIT model0 hyb E' (mrg Lh Sp) M ms' model').
    { apply (den_snap ASEGS LIMIT model0 (ms_mem ms') hyb E' _ M ms' model' HD').
      - intros w Hw. pose proof (proj1 (frz_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw) as Hw0.
        rewrite (Hfrzn w Hw0). symmetry. exact (Hfz' w Hw0).
      - intros w Hw Hout. unfold hyb, hyb_p.
        destruct (qndcell_b pz (bv_unsigned (Z_to_bv 64 w))) eqn:Eb; [reflexivity|].
        assert (Hw0 : own_pt E M w) by exact (proj1 (own_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw).
        assert (Hout0 : outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w)) by exact (outside_agree_shape _ E E' _ _ _ HbwS Ha' Hsh Hout).
        pose proof (Hw64 w Hw0) as Hw6.
        rewrite u_small64 in Eb by exact Hw6. symmetry. apply (Hkeep w Hw6 Hw0 Hout0).
        intros Hn. apply qndcell_b_spec in Hn. congruence. }
    (* [comment removed for export] *)
    assert (Hch : forall E'', agree (s_next (mrg Lh Sp)) E' E'' -> lden E'' (lconst 0x43d4c) = lden E'' (rget (s_regs (mrg Lh Sp)) (rk 1))).
    { intros E'' Ha''. pose proof (dn_sden _ _ _ _ _ _ _ _ _ HD3 E'' Ha'') as (_ & _ & _ & Hregs & _).
      specialize (Hregs (Z_to_bv 5 1)). cbn [restrict ms_regs] in Hregs. change (rkey (Z_to_bv 5 1)) with (rk 1) in Hregs.
      rewrite <- Hregs, Hrr. rewrite lden_lconst. replace (Z_to_bv 5 1) with (1%bv : reg) by (apply bv_eq; reflexivity). rewrite HRb1. reflexivity. }
    assert (Hrk : rk 1 <> xH) by (intros Hc0; vm_compute in Hc0; discriminate).
    pose proof (den_reg_eq ASEGS LIMIT model0 hyb E' _ M ms' model' (rk 1) (lconst 0x43d4c) HD3 Hrk Hch) as HD4.
    set (X := with_reg (mrg Lh Sp) (rk 1) (lconst 0x43d4c)) in *.
    pose proof (den_uncarve ASEGS LIMIT model0 hyb E' X M ms' model' _ _ l'' HD4 CpX Hsteps) as HD5.
    assert (HawLb : awf (s_next Lb) a = true) by (apply (awf_mono (s_next S)); [cbn [Lb nq_front s_next]; lia | exact Haw]).
    assert (Epz' : pden E' a = pz) by exact (pden_agree (s_next Lb) E E' a HawLb Ha').
    (* [comment removed for export] *)
    set (hyb1 := hyb_p (qndcell_b pz) m1 mem0).
    assert (Hh1_in : forall x, 0 <= x < 2^64 -> qndcell pz x -> hyb1 (wa x) = m1 (wa x)).
    { intros x Hx Hn. unfold hyb1, hyb_p. rewrite u_wa_small by exact Hx. rewrite (proj2 (qndcell_b_spec _ _) Hn). reflexivity. }
    assert (Hh1_out : forall x, 0 <= x < 2^64 -> ~ qndcell pz x -> hyb1 (wa x) = mem0 (wa x)).
    { intros x Hx Hn. unfold hyb1, hyb_p. rewrite u_wa_small by exact Hx.
      destruct (qndcell_b pz x) eqn:Eb; [exfalso; apply Hn; apply qndcell_b_spec; exact Eb | reflexivity]. }
    assert (Hhyb_out : forall x, 0 <= x < 2^64 -> ~ qndcell pz x -> hyb (wa x) = mem0 (wa x)).
    { intros x Hx Hn. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx.
      destruct (qndcell_b pz x) eqn:Eb; [exfalso; apply Hn; apply qndcell_b_spec; exact Eb | reflexivity]. }
    assert (Hhyb_m2 : forall x, 0 <= x < 2^64 -> qndcell pz x -> hyb (wa x) = m2 (wa x)).
    { intros x Hx Hn. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx. rewrite (proj2 (qndcell_b_spec _ _) Hn). apply Hvis. exact (proj2 (Hcelld x Hx Hn)). }
    (* [comment removed for export] *)
    assert (Hfoot_lo : forall x, pri_foot_z pz x -> 0 <= x < SP - 2064).
    { intros x Hf. pose proof (pri_foot_rng E a mem0 HI x Hf) as Hxr. split; [clear - Hxr; lia|].
      destruct Hf as [Hf|[Hf|[Hf|(c & Hc & Hf)]]].
      - clear - Hf G BT. fold SP in BT. fold CA in Hf, G. lia.
      - clear - Hf G BP B0. fold SP in BP. fold SB in Hf, B0. lia.
      - clear - Hf HSPr. lia.
      - pose proof (in_cls_rng c Hc) as Hcr. destruct (cls_jb pz mem0 HI c Hc) as (_ & _ & _ & Kz).
        clear - Hf G BP B0 S1 Hcr Kz. fold SP in BP. fold SB in Hf, B0, G. lia. }
    set (pz0 := qz_new pz sz).
    pose proof (iz_len _ _ HI) as Hlenz.
    assert (Hh1_m1 : forall x, 0 <= x < 2^64 -> qncell pz x -> hyb1 (wa x) = m1 (wa x)) by (intros x Hx Hq; exact (Hh1_in x Hx (or_introl Hq))).
    (* [comment removed for export] *)
    assert (HQh1 : q_inv hyb1 QC SB j 1 (sz + 8192)).
    { apply (q_inv_frame m1); [unfold QC; clear - B0; fold CA in B0; lia | unfold QC; clear - B1; lia | clear - B1; lia | clear - B1; lia | | | exact HQ1].
      - intros x Hx. apply Hh1_m1; [unfold QC in Hx; clear - Hx B0; fold CA in B0; lia | right; left; fold CA; unfold QC in Hx; clear - Hx; lia].
      - intros _ x Hx. apply Hh1_m1; [clear - Hx B1 Hj1 Hj32; lia | right; right; unfold BN; fold SB; fold j; exact Hx]. }
    assert (HIoh1 : INV_Co hyb1 CA SB 24 8192 1 32 (j + 1)).
    { apply (INV_Co_frame m1); [clear - B1; lia | clear - B1; lia | clear - B1; lia | clear - B1; lia | | exact (INV_G_o _ _ _ _ _ _ _ _ HIG1)].
      intros x Hf. apply Hh1_m1; [unfold foot_Co in Hf; clear - Hf B1; lia | left; left; exact Hf]. }
    assert (Hnq_gq : forall x, 930696 <= x < 930736 -> ~ qncell pz x).
    { intros x Hx. unfold qncell, ncell, foot_Co, BN. fold CA. fold SB. fold j. clear - Hx HCAf HSBf Hj1. lia. }
    assert (HPoh1 : POP_C hyb1 SB (z_sh pz) 24 8192 (j + 1)).
    { apply (POP_C_frame mem0); [| change (8192 / 8) with 1024; clear - Hj1; lia | exact (POP_C_step mem0 SB (z_sh pz) 24 8192 j ltac:(clear; lia) ltac:(clear - Hj1; lia) HPo)].
      intros x Hx. unfold RBX, SHX in Hx. change (8192 / 8) with 1024 in Hx. apply Hh1_out.
      - destruct Hx as [Hx|Hx]; [clear - Hx B1 Hj1; lia | clear - Hx S1 G Hj1; lia].
      - intros [Hq|[Hq|(Hg1 & Hq)]].
        + revert Hq. unfold qncell, ncell, foot_Co, BN. fold CA. fold SB. fold j. destruct Hx as [Hx|Hx].
          * clear - Hx T1 B0 B1 Hj1 Hj32. fold CA in T1, B0. fold SB in B0. lia.
          * clear - Hx S1 S2 T1 B0 B1 Hj1 Hj32. fold CA in S2, T1, B0. fold SB in B0. lia.
        + destruct Hx as [Hx|Hx]; [clear - Hx Hq B1 Hj1; lia | clear - Hx Hq S1 Hj1; lia].
        + specialize (Hgl0 Hg1). specialize (HGl Hg1). fold j in HGl. unfold BG in Hq. fold SB in Hq.
          destruct Hx as [Hx|Hx]; [clear - Hx Hq HGl; lia | clear - Hx Hq S1 B0 Hgl0; fold SB in B0; lia]. }
    assert (HSTh1 : STATS hyb1 CA).
    { destruct HIG1 as [_ _ _ _ _ _ _ _ _ _ _ (st & Hst3 & Rst) _ _ Wst].
      destruct HSTr as (_ & (st2 & Hst2 & Rst2) & Wst0).
      destruct (rdn_some m1 (CA + 2584) 8 ltac:(clear - B1; lia) ltac:(cbn; unfold two64; clear - B1; lia)) as (bs & Hbs).
      { intros i Hi. cbn in Hi.
        destruct (rd_byte (ms_mem msr) (CA + 2584) 8 st2 (Z.to_nat i) ltac:(clear - B1; lia) ltac:(cbn; clear - B1; lia) Rst2 ltac:(clear - Hi; lia)) as (b & _ & Xb). rewrite Z2Nat.id in Xb by (clear - Hi; lia).
        assert (X1 : rd1 ASEGS (ms_mem msr) (Z_to_bv 64 (CA + 2584 + i)) <> None).
        { unfold rd in Xb. cbn [rdn] in Xb. unfold rd1. unfold wa in Xb. destruct (ms_mem msr (Z_to_bv 64 (CA + 2584 + i))); [discriminate|].
          destruct (seg_rom ASEGS (Z_to_bv 64 (CA + 2584 + i))); [discriminate | discriminate]. }
        assert (X2 : wview ASEGS (ms_mem msr) (Z_to_bv 64 (CA + 2584 + i)) <> None).
        { pose proof (Wst0 (24 + i) 1%nat ltac:(clear - Hi; lia) ltac:(cbn; clear - Hi; lia)) as W. replace (CA + 2560 + (24 + i)) with (CA + 2584 + i) in W by ring.
          cbn [store_ok] in W. unfold wa in W. destruct (wview ASEGS (ms_mem msr) (Z_to_bv 64 (CA + 2584 + i))); [discriminate | discriminate]. }
        exact (proj1 (grows_rw ASEGS (ms_mem msr) m1 _ Hgr1 X1 X2)). }
      destruct (rd_exists m1 (CA + 2584) 8 bs ltac:(clear - B1; lia) Hbs) as (v & Hv1 & Hv2 & Hrd).
      assert (Hst_c : forall x, CA + 2560 <= x < CA + 2592 -> hyb1 (wa x) = m1 (wa x)).
      { intros x Hx. apply Hh1_m1; [clear - Hx B1; lia | left; right; exact Hx]. }
      split; [|split].
      - exists st. split; [exact Hst3|]. apply (rd_frame m1); [clear - B1; lia | cbn; clear - B1; lia | intros x Hx; cbn in Hx; apply Hst_c; clear - Hx; lia | exact Rst].
      - exists v. split; [clear - Hv1 Hv2; lia|]. apply (rd_frame m1); [clear - B1; lia | cbn; clear - B1; lia | intros x Hx; cbn in Hx; apply Hst_c; clear - Hx; lia | exact Hrd].
      - apply (wr_frame m1); [clear - B1; lia | clear - B1; lia | intros x Hx; apply Hst_c; clear - Hx; lia | exact Wst]. }
    assert (HWh1 : forall x, CA - 128 <= x < CA - 96 -> wview ASEGS hyb1 (wa x) <> None).
    { intros x Hx. rewrite (wview_same m1 hyb1) by (apply Hh1_m1; [clear - Hx B0; fold CA in B0; lia | right; left; fold CA; exact Hx]).
      apply (wr_byte m1 QC 32 x); [unfold QC; clear - B0; fold CA in B0; lia | unfold QC; clear - B1; lia | exact Hwq1 | unfold QC; clear - Hx; lia]. }
    assert (HI1 : INV_Az pz0 hyb1).
    { apply (INV_Az_qnew pz mem0 hyb1 sz HI Hdisj Hqn0 Hj1 Hjhi HQh1 HIoh1 HPoh1 HSTh1 HWh1).
      intros x Hf N1 N2 N3. destruct (Hfoot_lo x Hf) as [Hx0 Hxlo]. assert (Hx64 : 0 <= x < 2^64) by (clear - Hx0 Hxlo HSPr; lia).
      destruct (qndcell_b pz x) eqn:Eb; [|apply Hh1_out; [exact Hx64 | intros Hn; apply qndcell_b_spec in Hn; congruence]].
      apply qndcell_b_spec in Eb. rewrite (Hh1_in x Hx64 Eb).
      rewrite Hfr1'; [exact (proj1 (Hcelld x Hx64 Eb)) | exact Hx64 | clear - Hxlo; lia | exact N1 | unfold QC; clear - N2; lia | unfold BN in N3; fold SB in N3; fold j in N3; exact N3]. }
    (* [comment removed for export] *)
    assert (Ez0 : z_ca pz0 = CA /\ z_sb pz0 = SB /\ z_qj pz0 = j /\ z_qn pz0 = 1 /\ z_qb pz0 = sz + 8192 /\
                  z_gn pz0 = z_gn pz /\ z_gl pz0 = z_gl pz /\ z_gb pz0 = z_gb pz /\ z_tg pz0 = z_tg pz /\ z_pg pz0 = z_pg pz).
    { unfold pz0. rewrite (qnew_ca pz sz Hlenz), (qnew_sb pz sz Hlenz), (qnew_qj pz sz Hlenz), (qnew_qn pz sz Hlenz), (qnew_qb pz sz Hlenz),
        (qnew_gn pz sz Hlenz), (qnew_gl pz sz Hlenz), (qnew_gb pz sz Hlenz), (qnew_tg pz sz Hlenz), (qnew_pg pz sz Hlenz). repeat split; reflexivity. }
    destruct Ez0 as (Zca & Zsb & Zqj & Zqn & Zqb & Zgn & Zgl & Zgb & Ztg & Zpg).
    assert (Hl0 : List.length pz0 = PRI_LEN) by exact (qnew_len pz sz Hlenz).
    assert (Hfoot_eq : forall x, pri_foot_z (qz_drain pz0) x <-> pri_foot_z pz x).
    { intros x. rewrite (qdrain_foot pz0 Hl0 x). exact (qnew_foot pz sz Hlenz Z1 x). }
    assert (HIz' : INV_Az (qz_drain pz0) hyb).
    { apply (INV_Az_qdrain pz0 hyb1 hyb HI1); rewrite ?Zca, ?Zsb, ?Zqj, ?Zqn, ?Zqb, ?Zgn, ?Zgl, ?Zgb, ?Ztg, ?Zpg.
      - exact Hdisj.
      - clear. lia.
      - fold QC. apply (q_inv_frame m2); [unfold QC; clear - B0; fold CA in B0; lia | unfold QC; clear - B1; lia | clear - B1; lia | clear - B1; lia | | | exact HQ2].
        + intros x Hx. apply Hhyb_m2; [unfold QC in Hx; clear - Hx B0; fold CA in B0; lia | left; right; left; fold CA; unfold QC in Hx; clear - Hx; lia].
        + intros Hc0. exfalso. clear - Hc0. lia.
      - replace (z_gb pz + (sz + 8192)) with (sz + 8192 + z_gb pz) by ring.
        apply (gq_inv_o_frame m2); [clear - B1; lia | clear - B1; lia | | exact (gq_inv_to_o _ _ _ _ _ _ HG2)].
        intros x [Hx|(_ & Hx)]; apply Hhyb_m2.
        + clear - Hx. lia.
        + right. left. exact Hx.
        + clear - Hx B1 Hj1 Hj32. lia.
        + left. right. right. unfold BN. fold SB. fold j. clear - Hx. lia.
      - intros x Hx. rewrite (wview_same m2 hyb) by (apply Hhyb_m2; [clear - Hx B0; fold CA in B0; lia | left; right; left; fold CA; exact Hx]).
        apply (wr_byte m2 QC 32 x); [unfold QC; clear - B0; fold CA in B0; lia | unfold QC; clear - B1; lia | | unfold QC; clear - Hx; lia].
        intros d k Hd' Hk'. apply (store_ok_mono ASEGS k m1 m2 _ Hgr2). exact (Hwq1 d k Hd' Hk').
      - intros x Hf N1 N2 N3. apply (qnew_foot pz sz Hlenz Z1) in Hf. destruct (Hfoot_lo x Hf) as [Hx0 Hxlo].
        assert (Hx64 : 0 <= x < 2^64) by (clear - Hx0 Hxlo HSPr; lia).
        destruct (qndcell_b pz x) eqn:Eb.
        + apply qndcell_b_spec in Eb. rewrite (Hhyb_m2 x Hx64 Eb), (Hh1_in x Hx64 Eb).
          apply Hfr2; [exact Hx64 | clear - Hxlo; lia | unfold QC; clear - N1; lia | exact N2 |].
          intros (Hg1 & Hc0). apply N3. split; [exact Hg1 | unfold BG; rewrite Zsb, Zgl; exact Hc0].
        + assert (Hn : ~ qndcell pz x) by (intros Hn; apply qndcell_b_spec in Hn; congruence).
          rewrite (Hhyb_out x Hx64 Hn), (Hh1_out x Hx64 Hn). reflexivity. }
    set (pri' := q_step_drain (q_step_new a szl) a (p_j a QCLS) (laddc szl 8192)) in *.
    assert (Ha'' : a_qstep a pri' = a_with a pri') by reflexivity.
    set (a' := a_qstep a pri') in *.
    assert (Hwsz : lwf (s_next Lb) szl = true).
    { pose proof HwLb as XW. unfold state_wf in XW. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _].
      exact (regs_wf_n_spec _ _ 31 XW 14%nat ltac:(clear; lia)). }
    assert (Epz2 : pden E' a' = qz_drain pz0).
    { unfold a', pri'. rewrite (pden_qnew_drain E' a szl Hlen); rewrite ?Epz', ?(uE_agree (s_next Lb) E E' szl Hwsz Ha'); fold sz; fold j.
      - reflexivity.
      - clear - Hj1 Hj32. unfold two64. lia.
      - clear - Hnum. unfold two64. lia.
      - clear - Rgn Cgnhi Hgn0. unfold two64. lia.
      - clear - Hnum Hgn0. unfold two64. lia. }
    assert (Hne' : pri' <> []).
    { intros Hn. pose proof (f_equal (@List.length lin) Hn) as XL. unfold pri', q_step_drain, q_step_new, pri_step in XL. rewrite !set_nth_length, Hlen in XL. discriminate. }
    assert (Hbase : forall k, (k < 5)%nat -> nth k pri' lc0 = nth k (a_pri a) lc0).
    { intros k Hk5. unfold pri', q_step_drain, q_step_new, pri_step, QCLS. change (cidx 24) with 23%nat.
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia). replace (Nat.eqb k 70) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia). replace (Nat.eqb k 69) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia). replace (Nat.eqb k 68) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia). replace (Nat.eqb k 67) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia). replace (Nat.eqb k 66) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia). replace (Nat.eqb k 67) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia). replace (Nat.eqb k 66) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia). replace (Nat.eqb k 65) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia). replace (Nat.eqb k (6 + 2 * 23)) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite Hlen; unfold PRI_LEN; clear; lia). replace (Nat.eqb k (5 + 2 * 23)) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia). reflexivity. }
    assert (Hmono : forall x, pri_foot_z (pden E a) x -> pri_foot_z (pden E' (a_with a pri')) x).
    { intros x Hf. change (a_with a pri') with a'. rewrite Epz2. apply Hfoot_eq. exact Hf. }
    assert (Hdepf : forall x, 0 <= x < 2^64 -> downed (dD1 E a) (dB1 E a) x -> hyb (wa x) = mem0 (wa x)).
    { intros x Hx Hdw. apply (Hhyb_out x Hx). intros Hn.
      assert (F1 : pri_foot E a x).
      { destruct Hn as [[Hn|[Hn|Hn]]|[Hn|(Hg1 & Hn)]].
        - exact (proj1 (ncell_fp pz mem0 HI Hdisj 24 x in_cls_24 Z1 Hn)).
        - exact (proj1 (cb_fp pz mem0 HI Hdisj x ltac:(clear - Hn; lia))).
        - exact (proj1 (chunk_fp pz mem0 HI 24 x in_cls_24 Z1 Hjn ltac:(change (sz_tbl 24) with 8192; unfold BN in Hn; clear - Hn; lia))).
        - exact (proj1 (gq_fp pz mem0 HI x Hn)).
        - exact (proj1 (bg_fp pz mem0 HI Hg1 x ltac:(clear - Hn; lia))). }
      exact (pri_not_downed LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1 Hdw). }
    assert (Hext_step : forall b z, ext_sem (pden E a) b z -> ext_sem (pden E' (a_with a pri')) b z).
    { intros b z Hbz. change (a_with a pri') with a'. rewrite Epz2. apply (ext_sem_qdrain pz0 Hl0 ltac:(rewrite Zqn; clear; lia)).
      exact (ext_sem_qnew pz mem0 sz HI b z Hbz). }
    (* [comment removed for export] *)
    assert (Hext_fr : forall b z, ext_sem (pden E a) b z -> forall x, b <= x < b + z -> hyb (wa x) = mem0 (wa x)).
    { intros b z Hbz x Hxr. destruct (ext_sem_pt pz mem0 HI b z x Hbz Hxr) as (Rx & Hap & _ & HnQ & HnG).
      apply (Hhyb_out x ltac:(clear - Rx; lia)). intros Hn.
      destruct Hn as [[Hn|[Hn|Hn]]|[Hn|(Hg1 & Hn)]].
      - exact (proj1 (proj2 (proj2 (ncell_fp pz mem0 HI Hdisj 24 x in_cls_24 Z1 Hn))) Hap).
      - exact (proj1 (proj2 (proj2 (cb_fp pz mem0 HI Hdisj x ltac:(clear - Hn; lia)))) Hap).
      - exact (proj1 (proj2 (proj2 (chunk_fp pz mem0 HI 24 x in_cls_24 Z1 Hjn ltac:(change (sz_tbl 24) with 8192; unfold BN in Hn; clear - Hn; lia)))) Hap).
      - exact (proj1 (proj2 (proj2 (gq_fp pz mem0 HI x Hn))) Hap).
      - exact (HnG Hg1 ltac:(unfold BG in Hn; clear - Hn; lia)). }
    pose proof (HA_pri_step (s_next Lb) E E' M a mem0 hyb pri' HA0 HawLb Ha' Hne Hne' Hown_eq
                  ltac:(change (a_with a pri') with a'; rewrite Epz2; exact HIz') Hbase Hmono Hdepf Hext_step Hext_fr) as HA'.
    pose proof (own_pt_with (s_next Lb) E E' M a mem0 hyb pri' HA0 HawLb Ha' Hne Hown_eq
                  ltac:(change (a_with a pri') with a'; rewrite Epz2; exact HIz') Hbase Hmono) as Hsub.
    change (a_with a pri') with a' in HA', Hsub.
    (* [comment removed for export] *)
    set (Y := with_rgs X l'') in *.
    assert (HD8 : DEN ASEGS LIMIT model0 hyb E' Y (with_own M (a_own a')) ms' model').
    { apply (den_own_set ASEGS LIMIT model0 hyb hyb E' Y M ms' model' (a_own a') HD5).
      - apply forallb_forall. intros p Hp. rewrite forallb_forall in Cwo. specialize (Cwo p Hp). apply andb_prop in Cwo as [W1' W2'].
        apply andb_true_intro. split; apply (lwf_mono' (s_next S)); first [assumption | cbn [Y with_rgs X with_reg mrg Lh hand_post Lb nq_front s_next]; clear; lia].
      - intros w _. reflexivity.
      - intros w Hw. apply Hsub. exact (proj1 (own_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw).
      - intros w (q & Hq & Hqw). cbn [with_own sm_own] in Hq.
        assert (Hw0 : own_pt E M w).
        { rewrite (ha_aown _ _ _ _ HA') in Hq. unfold aown_of in Hq. apply in_app_or in Hq as [Hq|Hq].
          * exists q. split.
            + rewrite Hown_eq, (ha_aown _ _ _ _ HA0). unfold aown_of. apply in_or_app. left. exact Hq.
            + assert (Hpw : pwf (s_next Lb) q = true).
              { pose proof HawLb as XW. unfold awf in XW. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [_ XW].
                rewrite forallb_forall in XW. apply XW. rewrite (ha_aown _ _ _ _ HA0). unfold aown_of. apply in_or_app. left. exact Hq. }
              unfold pwf in Hpw. apply andb_prop in Hpw as [Hp1 Hp2]. rewrite <- (uE_agree _ E E' _ Hp1 Ha'), <- (uE_agree _ E E' _ Hp2 Ha'). exact Hqw.
          * assert (Hq' : In q (pri_own a')) by (change (a_pri a') with pri' in Hq; destruct pri'; [destruct Hq | exact Hq]).
            pose proof (pri_own_foot E' a' hyb ltac:(unfold INV_A; rewrite Epz2; exact HIz') q Hq' w Hqw) as Hf.
            unfold pri_foot in Hf. rewrite Epz2 in Hf. apply Hfoot_eq in Hf.
            apply (po_own _ _ _ _ HP0 w); [pose proof (pri_foot_rng E a mem0 HI w Hf) as Pr; clear - Pr; lia | exact Hf]. }
        pose proof (proj2 (own_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw0) as (q0 & Hq0 & Hq0w).
        exact (dn_own _ _ _ _ _ _ _ _ _ HD5 q0 Hq0 w Hq0w). }
    apply (Hk E' hyb ms' model').
    + apply (agree_mono _ (s_next Lb)); [cbn [Lb nq_front s_next]; clear; lia | exact Ha'].
    + intros q Hq w Hw. apply Hfrzn. exists q. split; [exact Hq | exact Hw].
    + exact HD8.
    + intros _. exact HA'.
Qed.
End NEnqDrain2.
(* [comment removed for export] *)
End AcNEnqD2.

Module AcNEnqN.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim StoreOk ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChFix FxChEnt FxWvC FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_put AXG_put3 AXG_np AXG_nf1 AXG_npf AXG_gp AXG_gf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_q1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_q3.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_q3e.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require NqTail.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_npf OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gf1 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AXG_gpf OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q3.AXG_q2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q3.AXG_q1e OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_q3e OSSVerify.Proofs.fast_float.from_chars.lib.AACB.NqTail.AXG_qt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarve AcSteps AcEntry AcMALp AcHand AcUnwApp0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDepDen AcAst AcHA AcFacts AcCarveP AcMALlib AcPutN AcUnwApp AcTbl.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConv AcConvG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep AcPriHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarveP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcOwnSet AcDenW AcConvA AcNPop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcNPopN AcNEnq.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcPutAppG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcShapes OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarveP OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPutN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcTblOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConv OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcRdw OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcPriDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarveP.AcStepsOut OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.AcAddOwn OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcOwnSet OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AcNPopApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AcRunApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNEnq.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import NqStepZ NqTail AcNEnqLib.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.



Section NEnqNode.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.

(* [comment removed for export] *)
Hypothesis batch_outside : forall mem0 E S M ms model a m0 jP jT, DEN ASEGS LIMIT model0 mem0 E S M ms model -> PRI_on E M a m0 ->
  find_grant (sm_maps M) (p_pg a) PG_SIZE = Some jP -> find_grant (sm_maps M) (p_tg a) TG_SIZE = Some jT ->
  forallb_l (fun R => pri_sep_c (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a R &&& batch_sep (s_facts S) a R) (s_rgs S) = true ->
  1 <= z_qn (pden E a) ->
  forall x, 0 <= x < two64 -> BQ (pden E a) <= x < BQ (pden E a) + 8192 -> outside E (s_rgs S) (Z_to_bv 64 x).

#[using="Hwx batch_outside"] Theorem nenq_node_room : forall S M a S' M' a', apost_nenq0 LIMIT S M a = Some (S', M', a') ->
  nq_room S a = true -> nq_nodrain S a = true ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx batch_outside : LiaFast.U) => LiaFast.u0).
  intros S M a S' M' a' H Hroom Hnd mem0 E ms model T Hd Haw HHA Hk.
  unfold nq_nodrain in Hnd. rewrite Hroom in Hnd. unfold nq_room in Hroom.
  unfold apost_nenq0 in H. cbv zeta in H. rewrite Hroom in H. rewrite Hnd in H.
  apply obool_some in H as (Hon & H).
  apply obind_some in H as (stk & Hstk & H). cbv beta in H.
  apply obind_some in H as (ro & Hro & H). cbv beta in H.
  apply obind_some in H as (ist & Hist & H). cbv beta in H.
  apply obind_some in H as (R & HR & H). cbv beta in H.
  apply obind_some in H as (o & Ho & H). cbv beta in H.
  apply obind_some in H as (cv & Hcv & H). cbv beta in H.
  apply obind_some in H as (jP & HjP & H). cbv beta in H.
  apply obind_some in H as (jT & HjT & H). cbv beta in H.
  apply obind_some in H as (gP & HgP & H). cbv beta in H.
  apply obool_some in H as (Hchk & H).
  apply obind_some in H as (l'' & Hsteps & H). cbv beta in H. injection H as <- <- <-.
  apply andb_prop in Hon as [Hon Hown_eq]. apply andb_prop in Hon as [Hon Hrs]. apply andb_prop in Hon as [Hon Hpc]. apply andb_prop in Hon as [Hon Hlen].
  apply Z.eqb_eq in Hpc. apply rsv_none_b_sound in Hrs. apply Nat.eqb_eq in Hlen.
  apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hown_eq.
  apply andb_prop in Hchk as [Hchk _]. apply andb_prop in Hchk as [Hchk Csep]. apply andb_prop in Hchk as [Hchk Cwo].
  apply andb_prop in Hchk as [Hchk Cwp]. apply andb_prop in Hchk as [Hchk CpX]. apply andb_prop in Hchk as [Hchk CwL].
  apply andb_prop in Hchk as [Hchk Cband]. apply andb_prop in Hchk as [Hchk Cge]. apply andb_prop in Hchk as [Hchk _].
  apply andb_prop in Hchk as [Hchk Csz40]. apply andb_prop in Hchk as [Hchk Cs6]. apply andb_prop in Hchk as [Hchk Ccase]. pose proof Hnd as Cnd. apply andb_prop in Hchk as [Hchk Csbw].
  apply andb_prop in Hchk as [Hchk Cst]. apply andb_prop in Hchk as [Hchk Cro]. apply andb_prop in Hchk as [Hchk Cwin].
  apply andb_prop in Hchk as [Hchk Csphi]. apply andb_prop in Hchk as [Hchk Csplo]. apply andb_prop in Hchk as [Hchk Cmod].
  apply andb_prop in Hchk as [Hchk Cra]. apply andb_prop in Hchk as [Hchk Cs1]. apply andb_prop in Hchk as [Hchk Ca1].
  apply andb_prop in Hchk as [Cperm Ca0].
  apply andb_prop in Ccase as [Ccase Cqjhi]. apply andb_prop in Ccase as [Cqnhi Cqjlo].
  apply lin_eqb_eq in Ca0, Ca1, Cs1, Cra. apply Z.leb_le in Csplo, Csphi, Cs6, Cnd, Cqnhi, Cqjlo, Cqjhi, Hroom.
  set (SPl := rget (s_regs S) (rk 2)) in *. set (szl := rget (s_regs S) (rk 14)) in *. set (s6l := rget (s_regs S) (rk 22)) in *.
  set (front := firstn 3 (carve_rgs cv)) in *. set (rest := skipn 3 (carve_rgs cv)) in *.
  set (L := nq_front S (s_next S) front) in *. set (Sp := nq_rest S rest) in *.
  set (Lb := nq_front S (s_next S + 66) front) in *.
  pose proof (HHA Hon) as HA0.
  assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hlen; discriminate).
  pose proof (ha_pri _ _ _ _ HA0 Hne) as HP0.
  (* [comment removed for export] *)
  pose proof (den_carve ASEGS LIMIT model0 mem0 E S M ms model _ _ _ cv Hd Hcv Cperm) as Hd1.
  assert (EQ1 : with_rgs S (carve_rgs cv) = mrg L Sp).
  { destruct S as [pc0 rg0 rgs0 fs0 nx0 rv0]. cbn [s_pc s_resv] in Hpc, Hrs. subst pc0 rv0.
    unfold with_rgs, mrg, L, Sp, nq_front, nq_rest. cbn [s_pc s_regs s_rgs s_facts s_next s_resv]. unfold front, rest. rewrite firstn_skipn. reflexivity. }
  rewrite EQ1 in Hd1.
  assert (EQb : bump (mrg L Sp) (s_next S + 66) = mrg Lb Sp) by reflexivity.
  pose proof (den_bump ASEGS LIMIT model0 mem0 E _ M ms model (s_next S + 66)%positive Hd1 ltac:(cbn [mrg s_next L nq_front]; lia)) as Hd2.
  rewrite EQb in Hd2.
  (* [comment removed for export] *)
  pose proof (po_inv _ _ _ _ HP0) as HI. unfold INV_A in HI. set (pz := pden E a) in *.
  pose proof (tg_pg_disj LIMIT model0 mem0 E S M ms model a mem0 Hd HP0) as Hdisj. fold pz in Hdisj.
  pose proof (az_geo pz mem0 HI) as G. destruct (q_seps pz mem0 HI Hdisj) as (T1 & S1 & S2 & B0).
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HRG & _ & HF0 & _).
  assert (Eqn : uE E (p_qn a) = z_qn pz) by (symmetry; apply zn_pden).
  assert (Eqb : uE E (p_qb a) = z_qb pz) by (symmetry; apply zn_pden).
  assert (Eqj : uE E (p_qj a) = z_qj pz) by (symmetry; apply zn_pden).
  assert (Eca : uE E (p_ca a) = z_ca pz) by (symmetry; apply zn_pden).
  assert (Esb : uE E (p_sb a) = z_sb pz) by (symmetry; apply zn_pden).
  pose proof (irange_sound E (s_facts S) (p_qn a) HF0) as Rqn. fold (uE E (p_qn a)) in Rqn. rewrite Eqn in Rqn.
  pose proof (irange_sound E (s_facts S) (p_qb a) HF0) as Rqb. fold (uE E (p_qb a)) in Rqb. rewrite Eqb in Rqb.
  pose proof (irange_sound E (s_facts S) szl HF0) as Rsz. fold (uE E szl) in Rsz.
  pose proof (irange_sound E (s_facts S) s6l HF0) as Rs6. fold (uE E s6l) in Rs6.
  pose proof (irange_sound E (s_facts S) SPl HF0) as Rsp. fold (uE E SPl) in Rsp.
  assert (Hqn1 : 1 <= z_qn pz <= 1020) by (clear - Rqn Hroom Cqnhi; lia).
  assert (Hal : uE E SPl mod 16 = 0) by (pose proof (fact_implied_ok E _ _ HF0 Cmod) as X; cbn [fact_ok] in X; exact X).
  destruct (iz_q _ _ HI) as [HQ0 HQj]. specialize (HQj ltac:(clear - Hqn1; lia)).
  (* [comment removed for export] *)
  assert (Rqf : fst (irange (s_facts S) (ladd (p_qb a) szl)) <= z_qb pz + uE E szl <= snd (irange (s_facts S) (ladd (p_qb a) szl))).
  { pose proof (irange_sound E (s_facts S) (ladd (p_qb a) szl) HF0) as X. rewrite ladd_u2 in X.
    - fold (uE E (p_qb a)) (uE E szl) in X. rewrite Eqb in X. exact X.
    - fold (uE E (p_qb a)) (uE E szl). rewrite Eqb. destruct HQ0 as (Hqb0 & _).
      assert (Y : snd (irange (s_facts S) szl) <= 2^40) by (first [exact Csz40 | apply Z.leb_le; exact Csz40]). clear - Hqb0 Y Rsz. unfold two64. lia. }
  cbv iota in Cnd.
  assert (Hqj0 : 0 <= z_qj pz < 32) by (destruct HQ0 as (_ & _ & [(Q0 & _)|(_ & Q2 & _)]); [clear - Q0 Hqn1; lia | exact Q2]).
  (* [comment removed for export] *)
  destruct (rg_hdr_b_sound _ _ _ _ Cwin) as (cw & Pw). destruct (ro_b_sound _ Cro) as (zro & Hzro & Pro).
  destruct (rg_hdr_b_sound _ _ _ _ Cst) as (cs & Pst).
  assert (HwLb : state_wf Lb = true) by (apply (nq_front_wf_mono S (s_next S) (s_next S + 66)%positive front ltac:(lia) CwL)).
  (* [comment removed for export] *)
  destruct (po_gp _ _ _ _ HP0) as (kp & Hgp). destruct (po_gt _ _ _ _ HP0) as (kt & Hgt).
  pose proof (band_hi LIMIT model0 mem0 E S M ms model SPl _ Hd Cband Hgp) as BP.
  pose proof (band_hi LIMIT model0 mem0 E S M ms model SPl _ Hd Cband Hgt) as BT.
  unfold gsz in BP, BT. cbn [fst snd] in BP, BT. unfold PG_SIZE, TG_SIZE in BP, BT. rewrite uE_lc in BP, BT by lia.
  assert (Epg : uE E (p_pg a) = z_pg pz) by (symmetry; apply zn_pden).
  assert (Etg : uE E (p_tg a) = z_tg pz) by (symmetry; apply zn_pden).
  rewrite Epg in BP. rewrite Etg in BT. fold (uE E SPl) in BP, BT.
  (* [comment removed for export] *)
  apply forallb_l_and3 in Csep.
  assert (Csep' : forallb_l (pri_sep_c (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a) (s_rgs (mrg L Sp)) = true).
  { clear - Csep. revert Csep. generalize (s_rgs (mrg L Sp)). intros l. induction l as [|R0 r IH]; [reflexivity|].
    cbn [forallb_l]. destruct (pri_sep_c (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a R0); [|discriminate].
    destruct (batch_sep (s_facts S) a R0); [exact IH | discriminate]. }
  assert (HCELL : forall x, 0 <= x < 2^64 -> qcell pz x -> own_pt E M x /\ outside E (s_rgs (mrg Lb Sp)) (wa x) /\ ~ frz_pt E M x).
  { intros x Hx [Hq|Hq].
    - destruct (cb_fp pz mem0 HI Hdisj x ltac:(clear - Hq; lia)) as (F1 & F2 & F3 & F4).
      split; [exact (po_own _ _ _ _ HP0 x Hx F1)|]. split.
      + exact (pri_outside_den LIMIT model0 mem0 E (mrg L Sp) M ms model a mem0 jP jT Hd1 HP0 HjP HjT Csep' x ltac:(unfold two64; lia) F2 F3).
      + exact (pri_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1).
    - destruct (bq_fp pz mem0 HI ltac:(clear - Hqn1; lia) x Hq) as (F1 & F2 & F4).
      split; [exact (po_own _ _ _ _ HP0 x Hx F1)|]. split.
      + exact (batch_outside mem0 E (mrg L Sp) M ms model a mem0 jP jT Hd1 HP0 HjP HjT Csep ltac:(fold pz; clear - Hqn1; lia) x ltac:(unfold two64; lia) Hq).
      + exact (pri_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1). }
  (* [comment removed for export] *)
  pose proof (dn_sden _ _ _ _ _ _ _ _ _ Hd2) as Hsd. pose proof (dn_own _ _ _ _ _ _ _ _ _ Hd2) as Hown.
  set (H := Hof E M model) in *. set (msr := restrict H ms) in *.
  pose proof (sden_0 _ _ _ _ Hsd) as Hd0.
  assert (Hsvc : ms_svc_pending ms = None) by (destruct Hd0 as (_ & X & _); exact X).
  assert (Hrv : ms_resv ms = None).
  { destruct Hd0 as (_ & _ & X & _). cbn [mrg s_resv Lb nq_front] in X. cbn [rsv_ok] in X. exact X. }
  set (SP := uE E SPl) in *. set (QC := z_ca pz - 128) in *. set (SB := z_sb pz) in *.
  assert (Ecb : uE E (l_cb a) = QC).
  { unfold l_cb. rewrite uE_laddc_z by (rewrite Eca; unfold two64; clear - B0; lia). rewrite Eca. reflexivity. }
  assert (R1 : getr (ms_regs ms) (Z_to_bv 5 1) = wa 278036).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 1) _ Hd0 Cra). rewrite lden_lconst. reflexivity. }
  assert (R2 : getr (ms_regs ms) (Z_to_bv 5 2) = wa SP).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 2) _ Hd0 eq_refl). unfold wa, SP, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R9 : getr (ms_regs ms) (Z_to_bv 5 9) = wa QC).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 9) _ Hd0 Cs1). rewrite <- Ecb. unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = wa QC).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 10) _ Hd0 Ca0). rewrite <- Ecb. unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R14 : getr (ms_regs ms) (Z_to_bv 5 14) = wa (uE E szl)).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 14) _ Hd0 eq_refl). unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R22 : getr (ms_regs ms) (Z_to_bv 5 22) = wa (uE E s6l)).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 22) _ Hd0 eq_refl). unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  (* [comment removed for export] *)
  pose proof (mrg_rg0 E Lb Sp msr 0%nat _ Hd0 Pw) as Rw.
  assert (HSPr : 2^46 + 8192 <= SP <= 2^47) by (clear - Rsp Csplo Csphi; unfold SP; lia).
  assert (Ebw : bv_unsigned (lden E (laddc SPl (-2064))) = SP - 2064) by (rewrite lden_laddc; fold (uE E SPl); fold SP; rewrite u_small64; unfold two64; clear - HSPr; lia).
  assert (Bw : forall x, SP - 2064 <= x < SP -> rd1 ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None /\ wview ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None).
  { intros x Hx. apply (rg_rw_pt _ _ _ x Rw eq_refl). cbn [rg_base]. rewrite Ebw. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; clear; lia). clear - Hx. lia. }
  assert (Hstko : stk_ok ASEGS (ms_mem msr) (wa SP) 2048).
  { intros a0 k Ha Hk'. rewrite u_wa_small in Ha, Hk' by (clear - HSPr; lia). apply store_ok_of_all; [pose proof (bv_unsigned_in_range _ a0) as Ra0; clear - Ra0 Ha Hk' HSPr; lia|].
    intros x Hx. pose proof (bv_unsigned_in_range _ x) as Rx. destruct (Bw (bv_unsigned x) ltac:(clear - Hx Ha Hk'; lia)) as [_ W]. rewrite Z_to_bv_bv_unsigned in W. exact W. }
  (* [comment removed for export] *)
  assert (Hcell : forall x, 0 <= x < 2^64 -> qcell pz x -> ms_mem msr (wa x) = mem0 (wa x) /\ H (wa x) = false).
  { intros x Hx Hc0. destruct (HCELL x Hx Hc0) as ((p & Hp & Hpw) & Hout & _). pose proof (Hown p Hp x Hpw) as [Hv Hm].
    fold H in Hv. unfold wa. split; [|exact Hv]. cbn [msr restrict ms_mem]. unfold mrestrict. rewrite Hv. apply Hm. exact Hout. }
  assert (IQ : q_inv (ms_mem msr) QC SB (z_qj pz) (z_qn pz) (z_qb pz)).
  { apply (q_inv_frame mem0); [unfold QC; clear - B0; lia | unfold QC; clear - B0; lia | unfold SB; clear - B0; lia | unfold SB; clear - B0; lia | | | exact HQ0].
    - intros x Hx. apply (Hcell x); [unfold QC in Hx; clear - Hx B0; lia | left; unfold QC in Hx; clear - Hx; lia].
    - intros _ x Hx. apply (Hcell x); [unfold SB in Hx; clear - Hx B0 Hqj0; lia | right; unfold BQ; exact Hx]. }
  assert (Hwq : wr (ms_mem msr) (QC + 24) 8).
  { apply (wr_frame mem0); [unfold QC; clear - B0; lia | unfold QC; clear - B0; lia | |].
    - intros x Hx. apply (Hcell x); [unfold QC in Hx; clear - Hx B0; lia | left; unfold QC in Hx; clear - Hx; lia].
    - intros d k Hd' Hk'. replace (QC + 24 + d) with (z_ca pz - 128 + (24 + d)) by (unfold QC; ring). apply (iz_wc _ _ HI); lia. }
  set (mp := bv_unsigned (getr (ms_regs ms) (Z_to_bv 5 13))).
  destruct (@qroom_contract (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_rom ms) (ms_mem msr) (ms_regs ms) QC SB (z_qj pz) (z_qn pz) (z_qb pz) (uE E szl) mp (uE E s6l) SP IQ Hqn1)
    as (R' & m' & Hms & HK & HQ' & Hmp & Hfr & Hgr).
  all: try (replace (1%bv : reg) with (Z_to_bv 5 1) by (apply bv_eq; reflexivity); exact R1).
  all: try (replace (2%bv : reg) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity); exact R2).
  all: try (replace (9%bv : reg) with (Z_to_bv 5 9) by (apply bv_eq; reflexivity); exact R9).
  all: try (replace (10%bv : reg) with (Z_to_bv 5 10) by (apply bv_eq; reflexivity); exact R10).
  all: try (replace (13%bv : reg) with (Z_to_bv 5 13) by (apply bv_eq; reflexivity); unfold mp, wa; rewrite Z_to_bv_bv_unsigned; reflexivity).
  all: try (replace (14%bv : reg) with (Z_to_bv 5 14) by (apply bv_eq; reflexivity); exact R14).
  all: try (replace (22%bv : reg) with (Z_to_bv 5 22) by (apply bv_eq; reflexivity); exact R22).
  all: try exact Hstko. all: try exact Hwq.
  all: try (split; [clear - HSPr; lia | exact Hal]).
  { pose proof (iz_ca _ _ HI) as (X1 & X2 & X3). fold pz in X1, X2, X3. unfold QC. split; [clear - X1; lia | clear - G BT HSPr; fold SP in BT; lia]. }
  { pose proof (iz_sb _ _ HI) as (X1 & X2). fold pz in X1, X2. unfold SB. split; [exact X1|]. split; [exact X2 | clear - G BP B0; fold SP in BP; lia]. }
  { unfold QC, SB. clear - T1 B0. lia. }
  { pose proof (uE_range E szl) as U1. pose proof (uE_range E s6l) as U2. pose proof (bv_unsigned_in_range _ (getr (ms_regs ms) (Z_to_bv 5 13))) as U3.
    destruct HQ0 as (Hqb0 & _). fold mp in U3. clear - U1 U2 U3 Hqb0 Rqb Rsz Rs6 Cnd Cs6 Rqf. unfold two64 in *. change (bv_modulus 64) with 18446744073709551616 in U3. lia. }
  assert (Hpc0 : ms_pc_val ms = wa 0x43e20) by (destruct Hd0 as (X & _); cbn [mrg s_pc Lb nq_front] in X; exact X).
  rewrite <- Hpc0 in Hms.
  assert (Est : uE E (laddc (p_tg a) 2872) = z_tg pz + 2872).
  { rewrite uE_laddc_z by (rewrite Etg; unfold two64; clear - G; lia). rewrite Etg. reflexivity. }
  apply (den_run_app cfg LIMIT model0 Hwx mem0 Lb Sp E M ms model T SPl (laddc (p_tg a) 2872) 0%nat 2%nat cw cs 0x43d4c KALLk
           [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat R' m' (qcell pz) 2064 ltac:(lia) Hd2 HwLb eq_refl Pw Pst).
  - fold SP. clear - HSPr. lia.
  - rewrite Est. clear - G BT HSPr. fold SP in BT. lia.
  - exact kall_cases.
  - exact Hms.
  - intros k Hk'. apply HK. clear - Hk'. unfold KQ. cbn [In] in *. intuition.
  - exact HCELL.
  - intros x Hx Hw _ Hq. apply Hfr; [exact Hx | fold SP in Hw; clear - Hw; lia | | |].
    + intros Hc0. apply Hq. left. unfold QC in Hc0. clear - Hc0. lia.
    + intros Hc0. apply Hq. right. unfold BQ. fold SB. clear - Hc0. lia.
    + intros Hc0. apply Hq. right. unfold BQ. fold SB. clear - Hc0 Hqn1. lia.
  - exact Hgr.
  - intros E' ms' model' HD' Ha' Hfz' Hrr Hvis.
    set (Lh := hand_post Lb 0x43d4c KALLk [0%nat; 2%nat]) in *.
    set (hyb := hyb_p (qcell_b pz) (ms_mem ms') mem0).
    assert (HwfM : sm_wf (s_next Lb) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd2).
    assert (HbwS : bases_wf (s_next Lb) (s_rgs (mrg Lb Sp)) = true) by exact (dn_bases _ _ _ _ _ _ _ _ _ Hd2).
    assert (Hsh : shape (s_rgs (mrg Lh Sp)) = shape (s_rgs (mrg Lb Sp))).
    { cbn [mrg s_rgs]. unfold Lh, hand_post. cbn [s_rgs]. unfold shape. rewrite !map_app. f_equal.
      pose proof (empty_at_shape [0%nat; 2%nat] (s_rgs Lb) 0) as Hs. unfold shape in Hs. exact Hs. }
    (* [comment removed for export] *)
    assert (Hnwin : forall w, outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w) -> 0 <= w < two64 -> ~ (SP - 2064 <= w < SP)).
    { intros w Hout Hw Hc0. unfold outside in Hout. rewrite Forall_forall in Hout. cbn [mrg s_rgs] in Hout.
      specialize (Hout _ ltac:(apply in_or_app; left; exact (nth_error_In _ _ Pw))). cbn [rg_base] in Hout.
      unfold rsz in Hout. cbn [rg_size] in Hout. rewrite lden_lconst, (u_small64 2064) in Hout by (unfold two64; clear; lia).
      rewrite Ebw in Hout. rewrite u_small64 in Hout by exact Hw. clear - Hout Hc0. lia. }
    (* [comment removed for export] *)
    assert (Hkeep : forall w, 0 <= w < two64 -> own_pt E M w -> outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w) ->
              ~ qcell pz w -> ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
    { intros w Hw (q & Hq & Hqw) Hout Hnc. destruct (Hown q Hq w Hqw) as [Hv Hm]. rewrite <- (Hm Hout). fold H in Hv.
      rewrite (Hvis _ Hv). change (Z_to_bv 64 w) with (wa w).
      rewrite Hfr; [cbn [msr restrict ms_mem]; unfold mrestrict, wa; rewrite Hv; reflexivity | unfold two64 in Hw; exact Hw | | | |].
      - pose proof (Hnwin w Hout Hw) as X. clear - X. lia.
      - intros Hc0. apply Hnc. left. unfold QC in Hc0. clear - Hc0. lia.
      - intros Hc0. apply Hnc. right. unfold BQ. fold SB. clear - Hc0. lia.
      - intros Hc0. apply Hnc. right. unfold BQ. fold SB. clear - Hc0 Hqn1. lia. }
    assert (Hfrzn : forall w, frz_pt E M w -> hyb (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
    { intros w Hw. unfold hyb, hyb_p. destruct (qcell_b _ _); [exact (Hfz' w Hw) | reflexivity]. }
    assert (Hw64 : forall w, own_pt E M w -> 0 <= w < two64).
    { intros w Hw0. destruct (Z_lt_le_dec w two64) as [X|X].
      - destruct Hw0 as (q & Hq & Hqw). pose proof (uE_range E (fst q)) as Uq. clear - Uq Hqw X. lia.
      - exfalso. destruct (ha_ownx _ _ _ _ HA0 w (own_pt_a_M E M a w Hown_eq Hw0)) as [Dc|[_ Pf]].
        + destruct HA0 as [(n0 & F0 & st0 & I0 & _) _ _ _ _ _ _]. destruct I0 as [_ _ _ D1r _ _ _ _ _ B1r _ _ _].
          unfold dcov in Dc. unfold two64 in X. clear - Dc X D1r B1r. lia.
        + pose proof (pri_foot_rng E a mem0 HI w Pf) as Pr. unfold two64 in X. clear - Pr X. lia. }
    assert (HD3 : DEN ASEGS LIMIT model0 hyb E' (mrg Lh Sp) M ms' model').
    { apply (den_snap ASEGS LIMIT model0 (ms_mem ms') hyb E' _ M ms' model' HD').
      - intros w Hw. pose proof (proj1 (frz_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw) as Hw0.
        rewrite (Hfrzn w Hw0). symmetry. exact (Hfz' w Hw0).
      - intros w Hw Hout. unfold hyb, hyb_p.
        destruct (qcell_b pz (bv_unsigned (Z_to_bv 64 w))) eqn:Eb; [reflexivity|].
        assert (Hw0 : own_pt E M w) by exact (proj1 (own_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw).
        assert (Hout0 : outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w)) by exact (outside_agree_shape _ E E' _ _ _ HbwS Ha' Hsh Hout).
        pose proof (Hw64 w Hw0) as Hw6.
        rewrite u_small64 in Eb by exact Hw6. symmetry. apply (Hkeep w Hw6 Hw0 Hout0).
        intros Hn. apply qcell_b_spec in Hn. congruence. }
    set (X := mrg Lh Sp) in *.
    pose proof (den_uncarve ASEGS LIMIT model0 hyb E' X M ms' model' _ _ l'' HD3 CpX Hsteps) as HD5.
    assert (HawLb : awf (s_next Lb) a = true) by (apply (awf_mono (s_next S)); [cbn [Lb nq_front s_next]; lia | exact Haw]).
    assert (Epz' : pden E' a = pz) by exact (pden_agree (s_next Lb) E E' a HawLb Ha').
    (* [comment removed for export] *)
    assert (Hhyb_in : forall x, 0 <= x < 2^64 -> qcell pz x -> hyb (wa x) = ms_mem ms' (wa x)).
    { intros x Hx Hn. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx. rewrite (proj2 (qcell_b_spec _ _) Hn). reflexivity. }
    assert (Hhyb_out : forall x, 0 <= x < 2^64 -> ~ qcell pz x -> hyb (wa x) = mem0 (wa x)).
    { intros x Hx Hn. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx.
      destruct (qcell_b pz x) eqn:Eb; [exfalso; apply Hn; apply qcell_b_spec; exact Eb | reflexivity]. }
    assert (Hhyb_m' : forall x, 0 <= x < 2^64 -> qcell pz x -> hyb (wa x) = m' (wa x)).
    { intros x Hx Hn. rewrite (Hhyb_in x Hx Hn). apply Hvis. exact (proj2 (Hcell x Hx Hn)). }
    set (sz := uE E szl) in *.
    assert (HQh : q_inv hyb QC SB (z_qj pz) (z_qn pz + 1) (z_qb pz + sz)).
    { apply (q_inv_frame m'); [unfold QC; clear - B0; lia | unfold QC; clear - B0; lia | unfold SB; clear - B0; lia | unfold SB; clear - B0; lia | | | exact HQ'].
      - intros x Hx. apply Hhyb_m'; [unfold QC in Hx; clear - Hx B0; lia | left; unfold QC in Hx; clear - Hx; lia].
      - intros _ x Hx. apply Hhyb_m'; [unfold SB in Hx; clear - Hx B0 Hqj0; lia | right; unfold BQ; exact Hx]. }
    assert (HWh : forall x, z_ca pz - 104 <= x < z_ca pz - 96 -> wview ASEGS hyb (wa x) <> None).
    { intros x Hx. rewrite (wview_same m' hyb) by (apply Hhyb_m'; [clear - Hx B0; lia | left; clear - Hx; lia]).
      apply (wr_byte m' (QC + 24) 8 x); [unfold QC; clear - B0; lia | unfold QC; clear - B0; lia | | unfold QC; clear - Hx; lia].
      intros d k Hd' Hk'. apply (store_ok_mono ASEGS k (ms_mem msr) m' _ Hgr). exact (Hwq d k Hd' Hk'). }
    assert (HIz' : INV_Az (qz_room pz sz) hyb).
    { apply (INV_Az_qroom pz mem0 hyb sz HI Hdisj ltac:(clear - Hqn1; lia) HQh HWh).
      intros x Hf N1 N2. pose proof (pri_foot_rng E a mem0 HI x Hf) as Hxr.
      destruct (qcell_b pz x) eqn:Eb; [|apply Hhyb_out; [clear - Hxr; lia | intros Hn; apply qcell_b_spec in Hn; congruence]].
      apply qcell_b_spec in Eb. rewrite (Hhyb_m' x ltac:(clear - Hxr; lia) Eb).
      pose proof (proj1 (Hcell x ltac:(clear - Hxr; lia) Eb)) as Hc0.
      destruct Eb as [Eb|Eb].
      - rewrite Hfr; [exact Hc0 | clear - Hxr; lia | | | |].
        + clear - Eb G BT HSPr. fold SP in BT. lia.
        + unfold QC. clear - Eb N1. lia.
        + unfold SB. clear - Eb T1 B0 Hqj0. lia.
        + unfold SB. clear - Eb T1 B0 Hqj0 Hqn1. lia.
      - (* [comment removed for export] *)
        assert (Eb8 : BQ pz <= x < BQ pz + 8) by (clear - Eb N2; lia). unfold BQ in Eb8. fold SB in Eb8.
        rewrite Hfr; [exact Hc0 | clear - Hxr; lia | | | |].
        + clear - Eb8 G BP HSPr B0 Hqj0. fold SP in BP. fold SB in G, B0. lia.
        + unfold QC. clear - Eb8 T1 B0 Hqj0. fold SB in B0. lia.
        + clear - Eb8. lia.
        + clear - Eb8 Hqn1. lia. }
    set (pri' := q_step_room a szl) in *.
    assert (Ha'' : a_qstep a pri' = a_with a pri') by reflexivity.
    set (a' := a_qstep a pri') in *.
    pose proof (iz_len _ _ HI) as Hlenz.
    assert (Epz2 : pden E' a' = qz_room pz sz).
    { unfold a', pri'. rewrite (pden_qroom E' a szl); rewrite ?Epz'.
      - rewrite (uE_agree (s_next Lb) E E' szl); [reflexivity | | exact Ha'].
        pose proof HwLb as XW. unfold state_wf in XW. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _].
        exact (regs_wf_n_spec _ _ 31 XW 14%nat ltac:(lia)).
      - clear - Hqn1. unfold two64. lia.
      - rewrite (uE_agree (s_next Lb) E E' szl); [destruct HQ0 as (Hqb0 & _); pose proof (uE_range E szl) as U1; fold sz in U1; clear - Hqb0 U1 Rqb Rsz Rs6 Cnd Cs6 Rqf; unfold two64 in *; lia | | exact Ha'].
        pose proof HwLb as XW. unfold state_wf in XW. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _].
        exact (regs_wf_n_spec _ _ 31 XW 14%nat ltac:(lia)). }
    assert (Hne' : pri' <> []).
    { intros Hn. pose proof (f_equal (@List.length lin) Hn) as XL. unfold pri', q_step_room in XL. rewrite !set_nth_length, Hlen in XL. discriminate. }
    assert (Hbase : forall k, (k < 5)%nat -> nth k pri' lc0 = nth k (a_pri a) lc0).
    { intros k Hk5. unfold pri', q_step_room.
      rewrite nth_set_nth by (rewrite set_nth_length, Hlen; unfold PRI_LEN; clear; lia).
      replace (Nat.eqb k 67) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite Hlen; unfold PRI_LEN; clear; lia).
      replace (Nat.eqb k 66) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia). reflexivity. }
    assert (Hmono : forall x, pri_foot_z (pden E a) x -> pri_foot_z (pden E' (a_with a pri')) x).
    { intros x Hf. change (a_with a pri') with a'. rewrite Epz2. apply (qroom_foot pz sz Hlenz). exact Hf. }
    assert (Hdepf : forall x, 0 <= x < 2^64 -> downed (dD1 E a) (dB1 E a) x -> hyb (wa x) = mem0 (wa x)).
    { intros x Hx Hdw. apply (Hhyb_out x Hx). intros Hn.
      assert (F1 : pri_foot E a x).
      { destruct Hn as [Hn|Hn]; [exact (proj1 (cb_fp pz mem0 HI Hdisj x ltac:(clear - Hn; lia))) | exact (proj1 (bq_fp pz mem0 HI ltac:(clear - Hqn1; lia) x Hn))]. }
      exact (pri_not_downed LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1 Hdw). }
    assert (Hext_step : forall b z, ext_sem (pden E a) b z -> ext_sem (pden E' (a_with a pri')) b z).
    { intros b z ((c & Hc & H1 & H2 & H3) & HB & HG). change (a_with a pri') with a'. rewrite Epz2. fold pz in H1, H2, HB, HG. split; [|split].
      - exists c. split; [exact Hc|]. rewrite (qroom_sb pz sz Hlenz), (qroom_j pz sz Hlenz c (in_cls_rng c Hc)). split; [exact H1|]. split; [exact H2 | exact H3].
      - intros _. rewrite (qroom_sb pz sz Hlenz), (qroom_qj pz sz Hlenz). apply HB. clear - Hqn1. lia.
      - rewrite (qroom_sb pz sz Hlenz), (qroom_gn pz sz Hlenz), (qroom_gl pz sz Hlenz). exact HG. }
    (* [comment removed for export] *)
    assert (Hext_fr : forall b z, ext_sem (pden E a) b z -> forall x, b <= x < b + z -> hyb (wa x) = mem0 (wa x)).
    { intros b z Hbz x Hxr. destruct (ext_sem_pt pz mem0 HI b z x Hbz Hxr) as (Rx & Hap & _ & HnQ & HnG).
      apply (Hhyb_out x ltac:(clear - Rx; lia)). intros Hn.
      destruct Hn as [Hn|Hn].
      - exact (proj1 (proj2 (proj2 (cb_fp pz mem0 HI Hdisj x ltac:(clear - Hn; lia)))) Hap).
      - exact (HnQ ltac:(clear - Hqn1; lia) ltac:(unfold BQ in Hn; clear - Hn; lia)). }
    pose proof (HA_pri_step (s_next Lb) E E' M a mem0 hyb pri' HA0 HawLb Ha' Hne Hne' Hown_eq
                  ltac:(change (a_with a pri') with a'; rewrite Epz2; exact HIz') Hbase Hmono Hdepf Hext_step Hext_fr) as HA'.
    pose proof (own_pt_with (s_next Lb) E E' M a mem0 hyb pri' HA0 HawLb Ha' Hne Hown_eq
                  ltac:(change (a_with a pri') with a'; rewrite Epz2; exact HIz') Hbase Hmono) as Hsub.
    change (a_with a pri') with a' in HA', Hsub.
    (* [comment removed for export] *)
    set (Y := with_rgs X l'') in *.
    assert (HD8 : DEN ASEGS LIMIT model0 hyb E' Y (with_own M (a_own a')) ms' model').
    { apply (den_own_set ASEGS LIMIT model0 hyb hyb E' Y M ms' model' (a_own a') HD5).
      - apply forallb_forall. intros p Hp. rewrite forallb_forall in Cwo. specialize (Cwo p Hp). apply andb_prop in Cwo as [W1' W2'].
        apply andb_true_intro. split; apply (lwf_mono' (s_next S)); first [assumption | cbn [Y with_rgs X mrg Lh hand_post Lb nq_front s_next]; lia].
      - intros w _. reflexivity.
      - intros w Hw. apply Hsub. exact (proj1 (own_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw).
      - intros w (q & Hq & Hqw). cbn [with_own sm_own] in Hq.
        assert (Hw0 : own_pt E M w).
        { rewrite (ha_aown _ _ _ _ HA') in Hq. unfold aown_of in Hq. apply in_app_or in Hq as [Hq|Hq].
          * (* [comment removed for export] *)
            exists q. split.
            + rewrite Hown_eq, (ha_aown _ _ _ _ HA0). unfold aown_of. apply in_or_app. left. exact Hq.
            + assert (Hpw : pwf (s_next Lb) q = true).
              { pose proof HawLb as XW. unfold awf in XW. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [_ XW].
                rewrite forallb_forall in XW. apply XW. rewrite (ha_aown _ _ _ _ HA0). unfold aown_of. apply in_or_app. left. exact Hq. }
              unfold pwf in Hpw. apply andb_prop in Hpw as [Hp1 Hp2]. rewrite <- (uE_agree _ E E' _ Hp1 Ha'), <- (uE_agree _ E E' _ Hp2 Ha'). exact Hqw.
          * assert (Hq' : In q (pri_own a')) by (change (a_pri a') with pri' in Hq; destruct pri'; [destruct Hq | exact Hq]).
            pose proof (pri_own_foot E' a' hyb ltac:(unfold INV_A; rewrite Epz2; exact HIz') q Hq' w Hqw) as Hf.
            unfold pri_foot in Hf. rewrite Epz2 in Hf. apply (qroom_foot pz sz Hlenz) in Hf.
            apply (po_own _ _ _ _ HP0 w); [pose proof (pri_foot_rng E a mem0 HI w Hf) as Pr; clear - Pr; lia | exact Hf]. }
        pose proof (proj2 (own_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw0) as (q0 & Hq0 & Hq0w).
        exact (dn_own _ _ _ _ _ _ _ _ _ HD5 q0 Hq0 w Hq0w). }
    apply (Hk E' hyb ms' model').
    + apply (agree_mono _ (s_next Lb)); [cbn [Lb nq_front s_next]; lia | exact Ha'].
    + intros q Hq w Hw. apply Hfrzn. exists q. split; [exact Hq | exact Hw].
    + exact HD8.
    + intros _. exact HA'.
Qed.
#[using="Hwx"] Theorem nenq_node_new : forall S M a S' M' a', apost_nenq0 LIMIT S M a = Some (S', M', a') ->
  nq_room S a = false -> nq_nodrain S a = true ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  1 <= z_j (pden E a) 24 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros S M a S' M' a' H Hroom Hnd mem0 E ms model T Hd Haw HHA Hj1 Hk.
  unfold nq_nodrain in Hnd. rewrite Hroom in Hnd. unfold nq_room in Hroom.
  unfold apost_nenq0 in H. cbv zeta in H. rewrite Hroom in H. rewrite Hnd in H.
  apply obool_some in H as (Hon & H).
  apply obind_some in H as (stk & Hstk & H). cbv beta in H.
  apply obind_some in H as (ro & Hro & H). cbv beta in H.
  apply obind_some in H as (ist & Hist & H). cbv beta in H.
  apply obind_some in H as (R & HR & H). cbv beta in H.
  apply obind_some in H as (o & Ho & H). cbv beta in H.
  apply obind_some in H as (cv & Hcv & H). cbv beta in H.
  apply obind_some in H as (jP & HjP & H). cbv beta in H.
  apply obind_some in H as (jT & HjT & H). cbv beta in H.
  apply obind_some in H as (gP & HgP & H). cbv beta in H.
  apply obool_some in H as (Hchk & H).
  apply obind_some in H as (l'' & Hsteps & H). cbv beta in H. injection H as <- <- <-.
  apply andb_prop in Hon as [Hon Hown_eq]. apply andb_prop in Hon as [Hon Hrs]. apply andb_prop in Hon as [Hon Hpc]. apply andb_prop in Hon as [Hon Hlen].
  apply Z.eqb_eq in Hpc. apply rsv_none_b_sound in Hrs. apply Nat.eqb_eq in Hlen.
  apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hown_eq.
  apply andb_prop in Hchk as [Hchk _]. apply andb_prop in Hchk as [Hchk Csep]. apply andb_prop in Hchk as [Hchk Cwo].
  apply andb_prop in Hchk as [Hchk Cwp]. apply andb_prop in Hchk as [Hchk CpX]. apply andb_prop in Hchk as [Hchk CwL].
  apply andb_prop in Hchk as [Hchk Cband]. apply andb_prop in Hchk as [Hchk Cge]. apply andb_prop in Hchk as [Hchk _].
  apply andb_prop in Hchk as [Hchk Csz40]. apply andb_prop in Hchk as [Hchk Cs6]. apply andb_prop in Hchk as [Hchk Ccase]. pose proof Hnd as Cnd. apply andb_prop in Hchk as [Hchk Csbw].
  apply andb_prop in Hchk as [Hchk Cst]. apply andb_prop in Hchk as [Hchk Cro]. apply andb_prop in Hchk as [Hchk Cwin].
  apply andb_prop in Hchk as [Hchk Csphi]. apply andb_prop in Hchk as [Hchk Csplo]. apply andb_prop in Hchk as [Hchk Cmod].
  apply andb_prop in Hchk as [Hchk Cra]. apply andb_prop in Hchk as [Hchk Cs1]. apply andb_prop in Hchk as [Hchk Ca1].
  apply andb_prop in Hchk as [Cperm Ca0].
  apply andb_prop in Ccase as [Ccase Cjb]. apply andb_prop in Ccase as [Cqn0 Cqb0].
  apply lin_eqb_eq in Ca0, Ca1, Cs1, Cra. apply Z.leb_le in Csplo, Csphi, Cs6, Cnd, Cjb. apply Z.eqb_eq in Cqn0, Cqb0.
  set (SPl := rget (s_regs S) (rk 2)) in *. set (szl := rget (s_regs S) (rk 14)) in *. set (s6l := rget (s_regs S) (rk 22)) in *.
  set (front := firstn 3 (carve_rgs cv)) in *. set (rest := skipn 3 (carve_rgs cv)) in *.
  set (L := nq_front S (s_next S) front) in *. set (Sp := nq_rest S rest) in *.
  set (Lb := nq_front S (s_next S + 66) front) in *.
  pose proof (HHA Hon) as HA0.
  assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hlen; discriminate).
  pose proof (ha_pri _ _ _ _ HA0 Hne) as HP0.
  (* [comment removed for export] *)
  pose proof (den_carve ASEGS LIMIT model0 mem0 E S M ms model _ _ _ cv Hd Hcv Cperm) as Hd1.
  assert (EQ1 : with_rgs S (carve_rgs cv) = mrg L Sp).
  { destruct S as [pc0 rg0 rgs0 fs0 nx0 rv0]. cbn [s_pc s_resv] in Hpc, Hrs. subst pc0 rv0.
    unfold with_rgs, mrg, L, Sp, nq_front, nq_rest. cbn [s_pc s_regs s_rgs s_facts s_next s_resv]. unfold front, rest. rewrite firstn_skipn. reflexivity. }
  rewrite EQ1 in Hd1.
  assert (EQb : bump (mrg L Sp) (s_next S + 66) = mrg Lb Sp) by reflexivity.
  pose proof (den_bump ASEGS LIMIT model0 mem0 E _ M ms model (s_next S + 66)%positive Hd1 ltac:(cbn [mrg s_next L nq_front]; lia)) as Hd2.
  rewrite EQb in Hd2.
  (* [comment removed for export] *)
  pose proof (po_inv _ _ _ _ HP0) as HI. unfold INV_A in HI. set (pz := pden E a) in *.
  pose proof (tg_pg_disj LIMIT model0 mem0 E S M ms model a mem0 Hd HP0) as Hdisj. fold pz in Hdisj.
  pose proof (az_geo pz mem0 HI) as G. destruct (q_seps pz mem0 HI Hdisj) as (T1 & S1 & S2 & B0).
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HRG & _ & HF0 & _).
  assert (Eqn : uE E (p_qn a) = z_qn pz) by (symmetry; apply zn_pden).
  assert (Eqb : uE E (p_qb a) = z_qb pz) by (symmetry; apply zn_pden).
  assert (Eca : uE E (p_ca a) = z_ca pz) by (symmetry; apply zn_pden).
  assert (Esb : uE E (p_sb a) = z_sb pz) by (symmetry; apply zn_pden).
  assert (Ej : uE E (p_j a 24) = z_j pz 24) by (symmetry; apply zn_pden).
  pose proof (irange_sound E (s_facts S) (p_qn a) HF0) as Rqn. fold (uE E (p_qn a)) in Rqn. rewrite Eqn in Rqn.
  pose proof (irange_sound E (s_facts S) (p_j a QCLS) HF0) as Rj. fold (uE E (p_j a QCLS)) in Rj. unfold QCLS in Rj, Cjb. rewrite Ej in Rj.
  pose proof (irange_sound E (s_facts S) szl HF0) as Rsz. fold (uE E szl) in Rsz.
  pose proof (irange_sound E (s_facts S) s6l HF0) as Rs6. fold (uE E s6l) in Rs6.
  pose proof (irange_sound E (s_facts S) SPl HF0) as Rsp. fold (uE E SPl) in Rsp.
  assert (Hal : uE E SPl mod 16 = 0) by (pose proof (fact_implied_ok E _ _ HF0 Cmod) as X; cbn [fact_ok] in X; exact X).
  destruct (iz_q _ _ HI) as [HQ0 _].
  (* [comment removed for export] *)
  assert (Rqf : fst (irange (s_facts S) (laddc szl 8192)) <= uE E szl + 8192 <= snd (irange (s_facts S) (laddc szl 8192))).
  { pose proof (irange_sound E (s_facts S) (laddc szl 8192) HF0) as X. fold (uE E (laddc szl 8192)) in X.
    assert (Y : snd (irange (s_facts S) szl) <= 2^40) by (first [exact Csz40 | apply Z.leb_le; exact Csz40]).
    rewrite uE_laddc_z in X by (pose proof (uE_range E szl) as U; clear - U Y Rsz; unfold two64 in *; lia). exact X. }
  cbv iota in Cnd.
  assert (Hqn0 : z_qn pz = 0 /\ z_qb pz = 0).
  { destruct HQ0 as (_ & _ & [(Q0 & Q1 & _)|(Q1 & _)]); [split; assumption | clear - Q1 Rqn Cqn0; lia]. }
  destruct Hqn0 as [Hqn0 Hqb0].
  assert (Hjhi : z_j pz 24 + 1 + mc_tbl 24 / 2 <= 262144 / sz_tbl 24) by (clear - Rj Cjb; lia).
  assert (Hj32 : z_j pz 24 + 2 <= 32) by (revert Hjhi; change (262144 / sz_tbl 24) with 32; change (mc_tbl 24 / 2) with 1; clear; lia).
  destruct (iz_cls _ _ HI 24 in_cls_24) as [(J0 & _)|(_ & Z1 & Jb & HIo & HPo)]; [clear - J0 Hj1; lia|].
  pose proof (iz_st _ _ HI) as HST.
  change (sz_tbl 24) with 8192 in HIo, HPo. change (mc_tbl 24 / 2) with 1 in HIo. change (262144 / 8192) with 32 in HIo.
  (* [comment removed for export] *)
  destruct (rg_hdr_b_sound _ _ _ _ Cwin) as (cw & Pw). destruct (ro_b_sound _ Cro) as (zro & Hzro & Pro).
  destruct (rg_hdr_b_sound _ _ _ _ Cst) as (cs & Pst).
  assert (HwLb : state_wf Lb = true) by (apply (nq_front_wf_mono S (s_next S) (s_next S + 66)%positive front ltac:(lia) CwL)).
  (* [comment removed for export] *)
  unfold sb_words_ok in Csbw. destruct (rdw IMGP (s_rgs S) (lconst 929848) 8) as [l1|] eqn:W1; [|discriminate].
  destruct (rdw IMGP (s_rgs S) (lconst 929864) 8) as [l2|] eqn:W2; [|discriminate].
  apply andb_prop in Csbw as [Q1 Q2]. apply lin_eqb_eq in Q1, Q2. subst l1 l2.
  pose proof (rdw_sound IMGP IMGP_ok E _ (s_rgs S) (lconst 929848) 8 _ HRG ltac:(lia) W1) as RSB.
  pose proof (rdw_sound IMGP IMGP_ok E _ (s_rgs S) (lconst 929864) 8 _ HRG ltac:(lia) W2) as RRIB.
  rewrite uE_lc in RSB, RRIB by lia. rewrite Esb in RSB.
  assert (Erip : uE E (l_rip a) = z_sb pz + 137438953472).
  { unfold l_rip. rewrite uE_laddc2 by (rewrite ?Esb; unfold two64; clear - G; lia). rewrite Esb. reflexivity. }
  rewrite Erip in RRIB.
  (* [comment removed for export] *)
  destruct (po_gp _ _ _ _ HP0) as (kp & Hgp). destruct (po_gt _ _ _ _ HP0) as (kt & Hgt).
  pose proof (band_hi LIMIT model0 mem0 E S M ms model SPl _ Hd Cband Hgp) as BP.
  pose proof (band_hi LIMIT model0 mem0 E S M ms model SPl _ Hd Cband Hgt) as BT.
  unfold gsz in BP, BT. cbn [fst snd] in BP, BT. unfold PG_SIZE, TG_SIZE in BP, BT. rewrite uE_lc in BP, BT by lia.
  assert (Epg : uE E (p_pg a) = z_pg pz) by (symmetry; apply zn_pden).
  assert (Etg : uE E (p_tg a) = z_tg pz) by (symmetry; apply zn_pden).
  rewrite Epg in BP. rewrite Etg in BT. fold (uE E SPl) in BP, BT.
  (* [comment removed for export] *)
  assert (Csep' : forallb_l (pri_sep_c (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a) (s_rgs (mrg L Sp)) = true).
  { clear - Csep. revert Csep. generalize (s_rgs (mrg L Sp)). intros l. induction l as [|R0 r IH]; [reflexivity|].
    cbn [forallb_l]. destruct (pri_sep_c (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a R0); [exact IH | discriminate]. }
  assert (Hjn : z_j pz 24 + 1 <= 262144 / sz_tbl 24) by (change (262144 / sz_tbl 24) with 32; clear - Hj32; lia).
  assert (HCELL : forall x, 0 <= x < 2^64 -> qncell pz x -> own_pt E M x /\ outside E (s_rgs (mrg Lb Sp)) (wa x) /\ ~ frz_pt E M x).
  { intros x Hx Hq.
    assert (F : pri_foot_z pz x /\ FPmax pz x /\ ~ alloc_part pz x).
    { destruct Hq as [Hq|[Hq|Hq]].
      - destruct (ncell_fp pz mem0 HI Hdisj 24 x in_cls_24 Z1 Hq) as (F1 & F2 & F3 & _). split; [exact F1|]. split; [exact F2 | exact F3].
      - destruct (cb_fp pz mem0 HI Hdisj x ltac:(clear - Hq; lia)) as (F1 & F2 & F3 & _). split; [exact F1|]. split; [exact F2 | exact F3].
      - destruct (chunk_fp pz mem0 HI 24 x in_cls_24 Z1 Hjn ltac:(change (sz_tbl 24) with 8192; unfold BN in Hq; clear - Hq; lia)) as (F1 & F2 & F3 & _).
        split; [exact F1|]. split; [exact F2 | exact F3]. }
    destruct F as (F1 & F2 & F3).
    split; [exact (po_own _ _ _ _ HP0 x Hx F1)|]. split.
    - exact (pri_outside_den LIMIT model0 mem0 E (mrg L Sp) M ms model a mem0 jP jT Hd1 HP0 HjP HjT Csep' x ltac:(unfold two64; lia) F2 F3).
    - exact (pri_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1). }
  (* [comment removed for export] *)
  pose proof (dn_sden _ _ _ _ _ _ _ _ _ Hd2) as Hsd. pose proof (dn_own _ _ _ _ _ _ _ _ _ Hd2) as Hown.
  set (H := Hof E M model) in *. set (msr := restrict H ms) in *.
  pose proof (sden_0 _ _ _ _ Hsd) as Hd0.
  assert (Hsvc : ms_svc_pending ms = None) by (destruct Hd0 as (_ & X & _); exact X).
  assert (Hrv : ms_resv ms = None).
  { destruct Hd0 as (_ & _ & X & _). cbn [mrg s_resv Lb nq_front] in X. cbn [rsv_ok] in X. exact X. }
  set (SP := uE E SPl) in *. set (CA := z_ca pz) in *. set (QC := CA - 128) in *. set (SB := z_sb pz) in *. set (j := z_j pz 24) in *.
  assert (Ecb : uE E (l_cb a) = QC).
  { unfold l_cb. rewrite uE_laddc_z by (rewrite Eca; unfold two64; clear - B0; fold CA in B0; lia). rewrite Eca. reflexivity. }
  assert (R1 : getr (ms_regs ms) (Z_to_bv 5 1) = wa 278036).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 1) _ Hd0 Cra). rewrite lden_lconst. reflexivity. }
  assert (R2 : getr (ms_regs ms) (Z_to_bv 5 2) = wa SP).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 2) _ Hd0 eq_refl). unfold wa, SP, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R9 : getr (ms_regs ms) (Z_to_bv 5 9) = wa QC).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 9) _ Hd0 Cs1). rewrite <- Ecb. unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = wa QC).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 10) _ Hd0 Ca0). rewrite <- Ecb. unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R11 : getr (ms_regs ms) (Z_to_bv 5 11) = wa CA).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 11) _ Hd0 Ca1). rewrite <- Eca. unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R14 : getr (ms_regs ms) (Z_to_bv 5 14) = wa (uE E szl)).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 14) _ Hd0 eq_refl). unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R22 : getr (ms_regs ms) (Z_to_bv 5 22) = wa (uE E s6l)).
  { change (ms_regs ms) with (ms_regs msr). rewrite (mrg_reg0 E Lb Sp msr (Z_to_bv 5 22) _ Hd0 eq_refl). unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  (* [comment removed for export] *)
  pose proof (mrg_rg0 E Lb Sp msr 0%nat _ Hd0 Pw) as Rw. pose proof (mrg_rg0 E Lb Sp msr 1%nat _ Hd0 Pro) as Rro.
  assert (HSPr : 2^46 + 8192 <= SP <= 2^47) by (clear - Rsp Csplo Csphi; unfold SP; lia).
  assert (Ebw : bv_unsigned (lden E (laddc SPl (-2064))) = SP - 2064) by (rewrite lden_laddc; fold (uE E SPl); fold SP; rewrite u_small64; unfold two64; clear - HSPr; lia).
  assert (Bw : forall x, SP - 2064 <= x < SP -> rd1 ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None /\ wview ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None).
  { intros x Hx. apply (rg_rw_pt _ _ _ x Rw eq_refl). cbn [rg_base]. rewrite Ebw. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; clear; lia). clear - Hx. lia. }
  assert (Hstko : stk_ok ASEGS (ms_mem msr) (wa SP) 2048).
  { intros a0 k Ha Hk'. rewrite u_wa_small in Ha, Hk' by (clear - HSPr; lia). apply store_ok_of_all; [pose proof (bv_unsigned_in_range _ a0) as Ra0; clear - Ra0 Ha Hk' HSPr; lia|].
    intros x Hx. pose proof (bv_unsigned_in_range _ x) as Rx. destruct (Bw (bv_unsigned x) ltac:(clear - Hx Ha Hk'; lia)) as [_ W]. rewrite Z_to_bv_bv_unsigned in W. exact W. }
  assert (Bro : forall i, 65536 <= i < 143360 -> ms_mem msr (Z_to_bv 64 i) = None) by exact (ro_none_z _ _ _ Hzro Rro).
  (* [comment removed for export] *)
  assert (Hcell : forall x, 0 <= x < 2^64 -> qncell pz x -> ms_mem msr (wa x) = mem0 (wa x) /\ H (wa x) = false).
  { intros x Hx Hc0. destruct (HCELL x Hx Hc0) as ((p & Hp & Hpw) & Hout & _). pose proof (Hown p Hp x Hpw) as [Hv Hm].
    fold H in Hv. unfold wa. split; [|exact Hv]. cbn [msr restrict ms_mem]. unfold mrestrict. rewrite Hv. apply Hm. exact Hout. }
  assert (B1 : 0 <= CA /\ CA + 4096 <= 2^63 /\ 0 <= SB /\ SB + 137438953472 + 4096 <= 2^63) by (unfold CA, SB; clear - B0; lia).
  assert (IQ : q_inv (ms_mem msr) QC SB (z_qj pz) 0 0).
  { rewrite <- Hqn0 at 1. rewrite <- Hqb0. apply (q_inv_frame mem0); [unfold QC; clear - B1 B0; fold CA in B0; lia | unfold QC; clear - B1; lia | clear - B1; lia | clear - B1; lia | | | exact HQ0].
    - intros x Hx. apply (Hcell x); [unfold QC in Hx; clear - Hx B0; fold CA in B0; lia | right; left; unfold QC in Hx; fold CA; clear - Hx; lia].
    - intros Hc0. exfalso. clear - Hc0 Hqn0. lia. }
  assert (HIor : INV_Co (ms_mem msr) CA SB 24 8192 1 32 j).
  { apply (INV_Co_frame mem0); [clear - B1; lia | clear - B1; lia | clear - B1; lia | clear - B1; lia | | exact HIo]. intros x Hf.
    assert (Hx : 0 <= x < 2^64) by (unfold foot_Co in Hf; clear - Hf B1; lia). exact (proj1 (Hcell x Hx (or_introl (or_introl Hf)))). }
  assert (HSTr : STATS (ms_mem msr) CA).
  { apply (STATS_frame mem0); [clear - B1; lia | clear - B1; lia | | exact HST]. intros x Hx. apply (Hcell x); [clear - Hx B1; lia | left; right; exact Hx]. }
  pose proof (INV_Co_G _ _ _ _ _ _ _ _ HIor) as HIG.
  assert (RSBr : rd (ms_mem msr) 929848 8 SB) by exact RSB.
  assert (RRIBr : rd (ms_mem msr) 929864 8 (SB + 137438953472)) by exact RRIB.
  specialize (HIG RSBr RRIBr HSTr).
  assert (Hwq : wr (ms_mem msr) QC 32).
  { apply (wr_frame mem0); [unfold QC; clear - B0; fold CA in B0; lia | unfold QC; clear - B1; lia | |].
    - intros x Hx. apply (Hcell x); [unfold QC in Hx; clear - Hx B0; fold CA in B0; lia | right; left; fold CA; unfold QC in Hx; clear - Hx; lia].
    - intros d k Hd' Hk'. replace (QC + d) with (z_ca pz - 128 + d) by (unfold QC, CA; ring). apply (iz_wc _ _ HI); lia. }
  assert (Hwb : wr (ms_mem msr) (SB + 103079215104 + 8192 * j) 8192).
  { apply wr_bytes; [clear - B1 Hj1; lia | clear - B1 Hj32; lia|]. intros x Hx.
    destruct (Hcell x ltac:(clear - Hx B1 Hj1 Hj32; lia) ltac:(right; right; unfold BN; fold SB; fold j; exact Hx)) as [Hm _].
    unfold wview. rewrite Hm. rewrite (pc_map _ _ _ _ _ _ HPo x ltac:(unfold RBX; fold SB; fold j; clear - Hx Hj32; lia)). discriminate. }
  set (mp := bv_unsigned (getr (ms_regs ms) (Z_to_bv 5 13))).
  destruct (@qnew_contract (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_rom ms) (ms_mem msr) (ms_regs ms) QC CA SB 1 32 j (z_qj pz) (uE E szl) mp (uE E s6l) SP IQ HIG
              ltac:(clear - Hj32; lia))
    as (R' & m' & Hms & HK & HQ' & HIG' & Hb0 & Hbmp & Hfr & Hgr).
  all: try (replace (1%bv : reg) with (Z_to_bv 5 1) by (apply bv_eq; reflexivity); exact R1).
  all: try (replace (2%bv : reg) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity); exact R2).
  all: try (replace (9%bv : reg) with (Z_to_bv 5 9) by (apply bv_eq; reflexivity); exact R9).
  all: try (replace (10%bv : reg) with (Z_to_bv 5 10) by (apply bv_eq; reflexivity); exact R10).
  all: try (replace (11%bv : reg) with (Z_to_bv 5 11) by (apply bv_eq; reflexivity); exact R11).
  all: try (replace (13%bv : reg) with (Z_to_bv 5 13) by (apply bv_eq; reflexivity); unfold mp, wa; rewrite Z_to_bv_bv_unsigned; reflexivity).
  all: try (replace (14%bv : reg) with (Z_to_bv 5 14) by (apply bv_eq; reflexivity); exact R14).
  all: try (replace (22%bv : reg) with (Z_to_bv 5 22) by (apply bv_eq; reflexivity); exact R22).
  all: try exact Hstko. all: try exact Hwq. all: try exact Hwb. all: try exact Bro. all: try reflexivity.
  all: try (split; [clear - HSPr; lia | exact Hal]).
  { pose proof (iz_ca _ _ HI) as (X1 & X2 & X3). fold pz in X1, X2, X3. fold CA in X1, X2, X3. split; [exact X1|]. split; [exact X2|]. clear - G BT HSPr. fold CA in G. lia. }
  { pose proof (iz_sb _ _ HI) as (X1 & X2). fold pz in X1, X2. fold SB in X1, X2. split; [exact X1|]. split; [exact X2 | clear - G BP B0; fold SB in G, B0; lia]. }
  { unfold QC. clear - T1 B0. fold CA in T1, B0. fold SB in B0. lia. }
  { pose proof (uE_range E szl) as U1. pose proof (uE_range E s6l) as U2. pose proof (bv_unsigned_in_range _ (getr (ms_regs ms) (Z_to_bv 5 13))) as U3.
    pose proof (irange_sound E (s_facts S) (p_qb a) HF0) as Rqb. fold (uE E (p_qb a)) in Rqb. rewrite Eqb, Hqb0 in Rqb.
    fold mp in U3. clear - U1 U2 U3 Rqb Rsz Rs6 Cnd Cs6 Rqf. unfold two64 in *. change (bv_modulus 64) with 18446744073709551616 in U3. lia. }
  assert (Hpc0 : ms_pc_val ms = wa 0x43e20) by (destruct Hd0 as (X & _); cbn [mrg s_pc Lb nq_front] in X; exact X).
  rewrite <- Hpc0 in Hms.
  assert (Est : uE E (laddc (p_tg a) 2872) = z_tg pz + 2872).
  { rewrite uE_laddc_z by (rewrite Etg; unfold two64; clear - G; lia). rewrite Etg. reflexivity. }
  apply (den_run_app cfg LIMIT model0 Hwx mem0 Lb Sp E M ms model T SPl (laddc (p_tg a) 2872) 0%nat 2%nat cw cs 0x43d4c KALLk
           [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat R' m' (qncell pz) 2064 ltac:(lia) Hd2 HwLb eq_refl Pw Pst).
  - fold SP. clear - HSPr. lia.
  - rewrite Est. clear - G BT HSPr. fold SP in BT. lia.
  - exact kall_cases.
  - exact Hms.
  - intros k Hk'. apply HK. exact Hk'.
  - exact HCELL.
  - intros x Hx Hw _ Hq. apply Hfr; [exact Hx | fold SP in Hw; clear - Hw; lia | | |].
    + intros Hc0. apply Hq. left. unfold owned_C in Hc0. unfold ncell, foot_Co. fold CA. fold SB. clear - Hc0. lia.
    + intros Hc0. apply Hq. right. left. fold CA. unfold QC in Hc0. clear - Hc0. lia.
    + intros Hc0. apply Hq. right. right. unfold BN. fold SB. fold j. clear - Hc0. lia.
  - exact Hgr.
  - intros E' ms' model' HD' Ha' Hfz' Hrr Hvis.
    set (Lh := hand_post Lb 0x43d4c KALLk [0%nat; 2%nat]) in *.
    set (hyb := hyb_p (qncell_b pz) (ms_mem ms') mem0).
    assert (HwfM : sm_wf (s_next Lb) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd2).
    assert (HbwS : bases_wf (s_next Lb) (s_rgs (mrg Lb Sp)) = true) by exact (dn_bases _ _ _ _ _ _ _ _ _ Hd2).
    assert (Hsh : shape (s_rgs (mrg Lh Sp)) = shape (s_rgs (mrg Lb Sp))).
    { cbn [mrg s_rgs]. unfold Lh, hand_post. cbn [s_rgs]. unfold shape. rewrite !map_app. f_equal.
      pose proof (empty_at_shape [0%nat; 2%nat] (s_rgs Lb) 0) as Hs. unfold shape in Hs. exact Hs. }
    assert (Hnwin : forall w, outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w) -> 0 <= w < two64 -> ~ (SP - 2064 <= w < SP)).
    { intros w Hout Hw Hc0. unfold outside in Hout. rewrite Forall_forall in Hout. cbn [mrg s_rgs] in Hout.
      specialize (Hout _ ltac:(apply in_or_app; left; exact (nth_error_In _ _ Pw))). cbn [rg_base] in Hout.
      unfold rsz in Hout. cbn [rg_size] in Hout. rewrite lden_lconst, (u_small64 2064) in Hout by (unfold two64; clear; lia).
      rewrite Ebw in Hout. rewrite u_small64 in Hout by exact Hw. clear - Hout Hc0. lia. }
    (* [comment removed for export] *)
    assert (Hfrq : forall x, 0 <= x < 2^64 -> ~ (SP - 2064 <= x < SP) -> ~ owned_C CA SB 24 x -> ~ (QC <= x < QC + 32) -> ~ (BN pz <= x < BN pz + 8192) ->
              m' (wa x) = ms_mem msr (wa x)).
    { intros x Hx N0 N1 N2 N3. apply Hfr; [exact Hx | clear - N0; lia | exact N1 | exact N2 | unfold BN in N3; fold SB in N3; fold j in N3; clear - N3; lia]. }
    assert (Hkeep : forall w, 0 <= w < two64 -> own_pt E M w -> outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w) ->
              ~ qncell pz w -> ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
    { intros w Hw (q & Hq & Hqw) Hout Hnc. destruct (Hown q Hq w Hqw) as [Hv Hm]. rewrite <- (Hm Hout). fold H in Hv.
      rewrite (Hvis _ Hv). change (Z_to_bv 64 w) with (wa w).
      rewrite Hfrq; [cbn [msr restrict ms_mem]; unfold mrestrict, wa; rewrite Hv; reflexivity | unfold two64 in Hw; exact Hw | exact (Hnwin w Hout Hw) | | |].
      - intros Hc0. apply Hnc. left. unfold owned_C in Hc0. unfold ncell, foot_Co. fold CA. fold SB. clear - Hc0. lia.
      - intros Hc0. apply Hnc. right. left. fold CA. unfold QC in Hc0. clear - Hc0. lia.
      - intros Hc0. apply Hnc. right. right. exact Hc0. }
    assert (Hfrzn : forall w, frz_pt E M w -> hyb (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
    { intros w Hw. unfold hyb, hyb_p. destruct (qncell_b _ _); [exact (Hfz' w Hw) | reflexivity]. }
    assert (Hw64 : forall w, own_pt E M w -> 0 <= w < two64).
    { intros w Hw0. destruct (Z_lt_le_dec w two64) as [X|X].
      - destruct Hw0 as (q & Hq & Hqw). pose proof (uE_range E (fst q)) as Uq. clear - Uq Hqw X. lia.
      - exfalso. destruct (ha_ownx _ _ _ _ HA0 w (own_pt_a_M E M a w Hown_eq Hw0)) as [Dc|[_ Pf]].
        + destruct HA0 as [(n0 & F0 & st0 & I0 & _) _ _ _ _ _ _]. destruct I0 as [_ _ _ D1r _ _ _ _ _ B1r _ _ _].
          unfold dcov in Dc. unfold two64 in X. clear - Dc X D1r B1r. lia.
        + pose proof (pri_foot_rng E a mem0 HI w Pf) as Pr. unfold two64 in X. clear - Pr X. lia. }
    assert (HD3 : DEN ASEGS LIMIT model0 hyb E' (mrg Lh Sp) M ms' model').
    { apply (den_snap ASEGS LIMIT model0 (ms_mem ms') hyb E' _ M ms' model' HD').
      - intros w Hw. pose proof (proj1 (frz_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw) as Hw0.
        rewrite (Hfrzn w Hw0). symmetry. exact (Hfz' w Hw0).
      - intros w Hw Hout. unfold hyb, hyb_p.
        destruct (qncell_b pz (bv_unsigned (Z_to_bv 64 w))) eqn:Eb; [reflexivity|].
        assert (Hw0 : own_pt E M w) by exact (proj1 (own_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw).
        assert (Hout0 : outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w)) by exact (outside_agree_shape _ E E' _ _ _ HbwS Ha' Hsh Hout).
        pose proof (Hw64 w Hw0) as Hw6.
        rewrite u_small64 in Eb by exact Hw6. symmetry. apply (Hkeep w Hw6 Hw0 Hout0).
        intros Hn. apply qncell_b_spec in Hn. congruence. }
    set (X := mrg Lh Sp) in *.
    pose proof (den_uncarve ASEGS LIMIT model0 hyb E' X M ms' model' _ _ l'' HD3 CpX Hsteps) as HD5.
    assert (HawLb : awf (s_next Lb) a = true) by (apply (awf_mono (s_next S)); [cbn [Lb nq_front s_next]; lia | exact Haw]).
    assert (Epz' : pden E' a = pz) by exact (pden_agree (s_next Lb) E E' a HawLb Ha').
    (* [comment removed for export] *)
    assert (Hhyb_in : forall x, 0 <= x < 2^64 -> qncell pz x -> hyb (wa x) = ms_mem ms' (wa x)).
    { intros x Hx Hn. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx. rewrite (proj2 (qncell_b_spec _ _) Hn). reflexivity. }
    assert (Hhyb_out : forall x, 0 <= x < 2^64 -> ~ qncell pz x -> hyb (wa x) = mem0 (wa x)).
    { intros x Hx Hn. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx.
      destruct (qncell_b pz x) eqn:Eb; [exfalso; apply Hn; apply qncell_b_spec; exact Eb | reflexivity]. }
    assert (Hhyb_m' : forall x, 0 <= x < 2^64 -> qncell pz x -> hyb (wa x) = m' (wa x)).
    { intros x Hx Hn. rewrite (Hhyb_in x Hx Hn). apply Hvis. exact (proj2 (Hcell x Hx Hn)). }
    set (sz := uE E szl) in *.
    assert (HQh : q_inv hyb QC SB j 1 (sz + 8192)).
    { apply (q_inv_frame m'); [unfold QC; clear - B0; fold CA in B0; lia | unfold QC; clear - B1; lia | clear - B1; lia | clear - B1; lia | | | exact HQ'].
      - intros x Hx. apply Hhyb_m'; [unfold QC in Hx; clear - Hx B0; fold CA in B0; lia | right; left; fold CA; unfold QC in Hx; clear - Hx; lia].
      - intros _ x Hx. apply Hhyb_m'; [clear - Hx B1 Hj1 Hj32; lia | right; right; unfold BN; fold SB; fold j; exact Hx]. }
    assert (HIoh : INV_Co hyb CA SB 24 8192 1 32 (j + 1)).
    { apply (INV_Co_frame m'); [clear - B1; lia | clear - B1; lia | clear - B1; lia | clear - B1; lia | | exact (INV_G_o _ _ _ _ _ _ _ _ HIG')].
      intros x Hf. apply Hhyb_m'; [unfold foot_Co in Hf; clear - Hf B1; lia | left; left; exact Hf]. }
    assert (HPoh : POP_C hyb SB (z_sh pz) 24 8192 (j + 1)).
    { apply (POP_C_frame mem0); [| change (8192 / 8) with 1024; clear - Hj1; lia | exact (POP_C_step mem0 SB (z_sh pz) 24 8192 j ltac:(clear; lia) ltac:(clear - Hj1; lia) HPo)].
      intros x Hx. unfold RBX, SHX in Hx. change (8192 / 8) with 1024 in Hx. apply Hhyb_out.
      - destruct Hx as [Hx|Hx]; [clear - Hx B1 Hj1; lia | clear - Hx S1 G Hj1; lia].
      - unfold qncell, ncell, foot_Co, BN. fold CA. fold SB. fold j. destruct Hx as [Hx|Hx].
        + clear - Hx T1 B0 B1 Hj1 Hj32. fold CA in T1, B0. fold SB in B0. lia.
        + clear - Hx S1 S2 T1 B0 B1 Hj1 Hj32. fold CA in S2, T1, B0. fold SB in B0. lia. }
    assert (HSTh : STATS hyb CA).
    { destruct HIG' as [_ _ _ _ _ _ _ _ _ _ _ (st & Hst3 & Rst) _ _ Wst].
      destruct HSTr as (_ & (st2 & Hst2 & Rst2) & Wst0).
      destruct (rdn_some m' (CA + 2584) 8 ltac:(clear - B1; lia) ltac:(cbn; unfold two64; clear - B1; lia)) as (bs & Hbs).
      { intros i Hi. cbn in Hi.
        destruct (rd_byte (ms_mem msr) (CA + 2584) 8 st2 (Z.to_nat i) ltac:(clear - B1; lia) ltac:(cbn; clear - B1; lia) Rst2 ltac:(clear - Hi; lia)) as (b & _ & Xb). rewrite Z2Nat.id in Xb by (clear - Hi; lia).
        assert (X1 : rd1 ASEGS (ms_mem msr) (Z_to_bv 64 (CA + 2584 + i)) <> None).
        { unfold rd in Xb. cbn [rdn] in Xb. unfold rd1. unfold wa in Xb. destruct (ms_mem msr (Z_to_bv 64 (CA + 2584 + i))); [discriminate|].
          destruct (seg_rom ASEGS (Z_to_bv 64 (CA + 2584 + i))); [discriminate | discriminate]. }
        assert (X2 : wview ASEGS (ms_mem msr) (Z_to_bv 64 (CA + 2584 + i)) <> None).
        { pose proof (Wst0 (24 + i) 1%nat ltac:(clear - Hi; lia) ltac:(cbn; clear - Hi; lia)) as W. replace (CA + 2560 + (24 + i)) with (CA + 2584 + i) in W by ring.
          cbn [store_ok] in W. unfold wa in W. destruct (wview ASEGS (ms_mem msr) (Z_to_bv 64 (CA + 2584 + i))); [discriminate | discriminate]. }
        exact (proj1 (grows_rw ASEGS (ms_mem msr) m' _ Hgr X1 X2)). }
      destruct (rd_exists m' (CA + 2584) 8 bs ltac:(clear - B1; lia) Hbs) as (v & Hv1 & Hv2 & Hrd).
      assert (Hst_c : forall x, CA + 2560 <= x < CA + 2592 -> hyb (wa x) = m' (wa x)).
      { intros x Hx. apply Hhyb_m'; [clear - Hx B1; lia | left; right; exact Hx]. }
      split; [|split].
      - exists st. split; [exact Hst3|]. apply (rd_frame m'); [clear - B1; lia | cbn; clear - B1; lia | intros x Hx; cbn in Hx; apply Hst_c; clear - Hx; lia | exact Rst].
      - exists v. split; [clear - Hv1 Hv2; lia|]. apply (rd_frame m'); [clear - B1; lia | cbn; clear - B1; lia | intros x Hx; cbn in Hx; apply Hst_c; clear - Hx; lia | exact Hrd].
      - apply (wr_frame m'); [clear - B1; lia | clear - B1; lia | intros x Hx; apply Hst_c; clear - Hx; lia | exact Wst]. }
    assert (HWh : forall x, CA - 128 <= x < CA - 96 -> wview ASEGS hyb (wa x) <> None).
    { intros x Hx. rewrite (wview_same m' hyb) by (apply Hhyb_m'; [clear - Hx B0; fold CA in B0; lia | right; left; fold CA; exact Hx]).
      apply (wr_byte m' QC 32 x); [unfold QC; clear - B0; fold CA in B0; lia | unfold QC; clear - B1; lia | | unfold QC; clear - Hx; lia].
      intros d k Hd' Hk'. apply (store_ok_mono ASEGS k (ms_mem msr) m' _ Hgr). exact (Hwq d k Hd' Hk'). }
    assert (HIz' : INV_Az (qz_new pz sz) hyb).
    { apply (INV_Az_qnew pz mem0 hyb sz HI Hdisj Hqn0 Hj1 Hjhi HQh HIoh HPoh HSTh HWh).
      intros x Hf N1 N2 N3. pose proof (pri_foot_rng E a mem0 HI x Hf) as Hxr.
      destruct (qncell_b pz x) eqn:Eb; [|apply Hhyb_out; [clear - Hxr; lia | intros Hn; apply qncell_b_spec in Hn; congruence]].
      apply qncell_b_spec in Eb. rewrite (Hhyb_m' x ltac:(clear - Hxr; lia) Eb).
      rewrite Hfrq; [exact (proj1 (Hcell x ltac:(clear - Hxr; lia) Eb)) | clear - Hxr; lia | | exact N1 | unfold QC; clear - N2; lia | exact N3].
      (* [comment removed for export] *)
      destruct Eb as [Eb|[Eb|Eb]].
      - unfold ncell, foot_Co in Eb. fold CA in Eb. fold SB in Eb. clear - Eb G BT BP HSPr B0. fold SP in BT, BP. fold CA in G, B0. fold SB in G, B0. lia.
      - fold CA in Eb. clear - Eb G BT HSPr. fold SP in BT. fold CA in G. lia.
      - unfold BN in Eb. fold SB in Eb. fold j in Eb. clear - Eb G BP HSPr B0 Hj32. fold SP in BP. fold SB in G, B0. lia. }
    set (pri' := q_step_new a szl) in *.
    assert (Ha'' : a_qstep a pri' = a_with a pri') by reflexivity.
    set (a' := a_qstep a pri') in *.
    pose proof (iz_len _ _ HI) as Hlenz.
    assert (Hwsz : lwf (s_next Lb) szl = true).
    { pose proof HwLb as XW. unfold state_wf in XW. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _].
      exact (regs_wf_n_spec _ _ 31 XW 14%nat ltac:(lia)). }
    assert (Hsz40 : 0 <= sz <= 2^40).
    { pose proof (uE_range E szl) as U1. fold sz in U1, Rsz. pose proof (irange_sound E (s_facts S) (p_qb a) HF0) as Rqb. fold (uE E (p_qb a)) in Rqb. rewrite Eqb, Hqb0 in Rqb.
      clear - U1 Rqb Rsz Rs6 Cnd Cs6 Rqf. lia. }
    assert (Epz2 : pden E' a' = qz_new pz sz).
    { unfold a', pri'. rewrite (pden_qnew E' a szl Hlen); rewrite ?Epz', ?(uE_agree (s_next Lb) E E' szl Hwsz Ha').
      - reflexivity.
      - fold j. clear - Hj1 Hj32. unfold two64. lia.
      - fold sz. clear - Hsz40. unfold two64. lia. }
    assert (Hne' : pri' <> []).
    { intros Hn. pose proof (f_equal (@List.length lin) Hn) as XL. unfold pri', q_step_new, pri_step in XL. rewrite !set_nth_length, Hlen in XL. discriminate. }
    assert (Hbase : forall k, (k < 5)%nat -> nth k pri' lc0 = nth k (a_pri a) lc0).
    { intros k Hk5. unfold pri', q_step_new, pri_step, QCLS. change (cidx 24) with 23%nat.
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia).
      replace (Nat.eqb k 67) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia).
      replace (Nat.eqb k 66) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia).
      replace (Nat.eqb k 65) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia).
      replace (Nat.eqb k (6 + 2 * 23)) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
      rewrite nth_set_nth by (rewrite Hlen; unfold PRI_LEN; clear; lia).
      replace (Nat.eqb k (5 + 2 * 23)) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia). reflexivity. }
    assert (Hmono : forall x, pri_foot_z (pden E a) x -> pri_foot_z (pden E' (a_with a pri')) x).
    { intros x Hf. change (a_with a pri') with a'. rewrite Epz2. apply (qnew_foot pz sz Hlenz Z1). exact Hf. }
    assert (Hdepf : forall x, 0 <= x < 2^64 -> downed (dD1 E a) (dB1 E a) x -> hyb (wa x) = mem0 (wa x)).
    { intros x Hx Hdw. apply (Hhyb_out x Hx). intros Hn.
      assert (F1 : pri_foot E a x).
      { destruct Hn as [Hn|[Hn|Hn]].
        - exact (proj1 (ncell_fp pz mem0 HI Hdisj 24 x in_cls_24 Z1 Hn)).
        - exact (proj1 (cb_fp pz mem0 HI Hdisj x ltac:(clear - Hn; lia))).
        - exact (proj1 (chunk_fp pz mem0 HI 24 x in_cls_24 Z1 Hjn ltac:(change (sz_tbl 24) with 8192; unfold BN in Hn; clear - Hn; lia))). }
      exact (pri_not_downed LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1 Hdw). }
    assert (Hext_step : forall b z, ext_sem (pden E a) b z -> ext_sem (pden E' (a_with a pri')) b z).
    { intros b z Hbz. change (a_with a pri') with a'. rewrite Epz2. exact (ext_sem_qnew pz mem0 sz HI b z Hbz). }
    (* [comment removed for export] *)
    assert (Hext_fr : forall b z, ext_sem (pden E a) b z -> forall x, b <= x < b + z -> hyb (wa x) = mem0 (wa x)).
    { intros b z Hbz x Hxr. destruct (ext_sem_pt pz mem0 HI b z x Hbz Hxr) as (Rx & Hap & _ & HnQ & HnG).
      apply (Hhyb_out x ltac:(clear - Rx; lia)). intros Hn.
      destruct Hn as [Hn|[Hn|Hn]].
      - exact (proj1 (proj2 (proj2 (ncell_fp pz mem0 HI Hdisj 24 x in_cls_24 Z1 Hn))) Hap).
      - exact (proj1 (proj2 (proj2 (cb_fp pz mem0 HI Hdisj x ltac:(clear - Hn; lia)))) Hap).
      - exact (proj1 (proj2 (proj2 (chunk_fp pz mem0 HI 24 x in_cls_24 Z1 Hjn ltac:(change (sz_tbl 24) with 8192; unfold BN in Hn; clear - Hn; lia)))) Hap). }
    pose proof (HA_pri_step (s_next Lb) E E' M a mem0 hyb pri' HA0 HawLb Ha' Hne Hne' Hown_eq
                  ltac:(change (a_with a pri') with a'; rewrite Epz2; exact HIz') Hbase Hmono Hdepf Hext_step Hext_fr) as HA'.
    pose proof (own_pt_with (s_next Lb) E E' M a mem0 hyb pri' HA0 HawLb Ha' Hne Hown_eq
                  ltac:(change (a_with a pri') with a'; rewrite Epz2; exact HIz') Hbase Hmono) as Hsub.
    change (a_with a pri') with a' in HA', Hsub.
    (* [comment removed for export] *)
    set (Y := with_rgs X l'') in *.
    assert (HD8 : DEN ASEGS LIMIT model0 hyb E' Y (with_own M (a_own a')) ms' model').
    { apply (den_own_set ASEGS LIMIT model0 hyb hyb E' Y M ms' model' (a_own a') HD5).
      - apply forallb_forall. intros p Hp. rewrite forallb_forall in Cwo. specialize (Cwo p Hp). apply andb_prop in Cwo as [W1' W2'].
        apply andb_true_intro. split; apply (lwf_mono' (s_next S)); first [assumption | cbn [Y with_rgs X mrg Lh hand_post Lb nq_front s_next]; lia].
      - intros w _. reflexivity.
      - intros w Hw. apply Hsub. exact (proj1 (own_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw).
      - intros w (q & Hq & Hqw). cbn [with_own sm_own] in Hq.
        assert (Hw0 : own_pt E M w).
        { rewrite (ha_aown _ _ _ _ HA') in Hq. unfold aown_of in Hq. apply in_app_or in Hq as [Hq|Hq].
          * exists q. split.
            + rewrite Hown_eq, (ha_aown _ _ _ _ HA0). unfold aown_of. apply in_or_app. left. exact Hq.
            + assert (Hpw : pwf (s_next Lb) q = true).
              { pose proof HawLb as XW. unfold awf in XW. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [_ XW].
                rewrite forallb_forall in XW. apply XW. rewrite (ha_aown _ _ _ _ HA0). unfold aown_of. apply in_or_app. left. exact Hq. }
              unfold pwf in Hpw. apply andb_prop in Hpw as [Hp1 Hp2]. rewrite <- (uE_agree _ E E' _ Hp1 Ha'), <- (uE_agree _ E E' _ Hp2 Ha'). exact Hqw.
          * assert (Hq' : In q (pri_own a')) by (change (a_pri a') with pri' in Hq; destruct pri'; [destruct Hq | exact Hq]).
            pose proof (pri_own_foot E' a' hyb ltac:(unfold INV_A; rewrite Epz2; exact HIz') q Hq' w Hqw) as Hf.
            unfold pri_foot in Hf. rewrite Epz2 in Hf. apply (qnew_foot pz sz Hlenz Z1) in Hf.
            apply (po_own _ _ _ _ HP0 w); [pose proof (pri_foot_rng E a mem0 HI w Hf) as Pr; clear - Pr; lia | exact Hf]. }
        pose proof (proj2 (own_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw0) as (q0 & Hq0 & Hq0w).
        exact (dn_own _ _ _ _ _ _ _ _ _ HD5 q0 Hq0 w Hq0w). }
    apply (Hk E' hyb ms' model').
    + apply (agree_mono _ (s_next Lb)); [cbn [Lb nq_front s_next]; lia | exact Ha'].
    + intros q Hq w Hw. apply Hfrzn. exists q. split; [exact Hq | exact Hw].
    + exact HD8.
    + intros _. exact HA'.
Qed.
End NEnqNode.
(* [comment removed for export] *)
End AcNEnqN.

Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NEnqFirst.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis Hsegb : segs_below_b ASEGS 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved ASEGS).
Hypothesis Hreswf : ivs_wf (segments_reserved ASEGS).

#[using="Hwx Hsegb Hoff Hrespos Hreswf"] Theorem nenq_node_first : forall S M a S' M' a', apost_nenq0 LIMIT S M a = Some (S', M', a') ->
  nq_room S a = false -> nq_nodrain S a = true ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  z_j (pden E a) 24 = 0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros S M a S' M' a' H Hroom Hnd mem0 E ms model T Hd Haw HHA Hj0 Hk.
  unfold nq_nodrain in Hnd. rewrite Hroom in Hnd. unfold nq_room in Hroom.
  unfold apost_nenq0 in H. cbv zeta in H. rewrite Hroom in H. rewrite Hnd in H.
  (* [comment removed for export] *)
  set (c := QCLS) in *. assert (Hc24 : c = 24) by reflexivity. clearbody c.
  apply obool_some in H as (Hon & H).
  apply obind_some in H as (stk & Hstk & H). cbv beta in H.
  apply obind_some in H as (ro & Hro & H). cbv beta in H.
  apply obind_some in H as (ist & Hist & H). cbv beta in H.
  apply obind_some in H as (R & HR & H). cbv beta in H.
  apply obind_some in H as (o & Ho & H). cbv beta in H.
  apply obind_some in H as (cv & Hcv & H). cbv beta in H.
  apply obind_some in H as (jP & HjP & H). cbv beta in H.
  apply obind_some in H as (jT & HjT & H). cbv beta in H.
  apply obind_some in H as (gP & HgP & H). cbv beta in H.
  apply obool_some in H as (Hchk & H).
  apply obind_some in H as (l'' & Hsteps & H). cbv beta in H. injection H as <- <- <-.
  apply andb_prop in Hon as [Hon Hown_eq]. apply andb_prop in Hon as [Hon Hrs]. apply andb_prop in Hon as [Hon Hpc]. apply andb_prop in Hon as [Hon Hlen].
  apply Z.eqb_eq in Hpc. apply rsv_none_b_sound in Hrs. apply Nat.eqb_eq in Hlen.
  apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hown_eq.
  assert (Hcin : In c CLS) by (rewrite Hc24; exact in_cls_24).
  apply andb_prop in Hchk as [Hchk Cfu]. apply andb_prop in Hchk as [Hchk Csep0]. apply andb_prop in Hchk as [Hchk Cwo].
  apply andb_prop in Hchk as [Hchk Cwp]. apply andb_prop in Hchk as [Hchk CpX]. apply andb_prop in Hchk as [Hchk CwL].
  apply andb_prop in Hchk as [Hchk Cband]. apply andb_prop in Hchk as [Hchk Cge]. apply andb_prop in Hchk as [Hchk _].
  apply andb_prop in Hchk as [Hchk Csz40]. apply andb_prop in Hchk as [Hchk Cs6]. apply andb_prop in Hchk as [Hchk Ccase]. pose proof Hnd as Cnd. apply andb_prop in Hchk as [Hchk Csbw].
  apply andb_prop in Hchk as [Hchk Cst]. apply andb_prop in Hchk as [Hchk Cro]. apply andb_prop in Hchk as [Hchk Cwin].
  apply andb_prop in Hchk as [Hchk Csphi]. apply andb_prop in Hchk as [Hchk Csplo]. apply andb_prop in Hchk as [Hchk Cmod].
  apply andb_prop in Hchk as [Hchk Cra]. apply andb_prop in Hchk as [Hchk Cs1]. apply andb_prop in Hchk as [Hchk Ca1].
  apply andb_prop in Hchk as [Cperm Ca0].
  apply andb_prop in Ccase as [Ccase Cjb]. apply andb_prop in Ccase as [Cqn0 Cqb0].
  apply lin_eqb_eq in Ca0, Ca1, Cs1, Cra. apply Z.leb_le in Csplo, Csphi, Cs6, Csz40, Cnd, Cjb. apply Z.eqb_eq in Cqn0, Cqb0.
  set (szl := rget (s_regs S) (rk 14)) in *. set (s6l := rget (s_regs S) (rk 22)) in *.
  set (SPl := rget (s_regs S) (rk 2)) in *.
  set (front := firstn 3 (carve_rgs cv)) in *. set (rest := skipn 3 (carve_rgs cv)) in *.
  set (L := nq_front S (s_next S) front) in *. set (Sp := nq_rest S rest) in *.
  set (Lb := nq_front S (s_next S + 66) front) in *.
  assert (Csep : forallb_l (pri_sep_c (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a) (s_rgs (mrg L Sp)) = true).
  { clear - Csep0. revert Csep0. generalize (s_rgs (mrg L Sp)). intros l. induction l as [|R0 r IH]; [reflexivity|].
    cbn [forallb_l]. destruct (pri_sep_c (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a R0); [exact IH | discriminate]. }
  rewrite <- Hc24 in Hj0.
  pose proof (HHA Hon) as HA0.
  assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hlen; discriminate).
  pose proof (ha_pri _ _ _ _ HA0 Hne) as HP0.
  (* [comment removed for export] *)
  pose proof (den_carve ASEGS LIMIT model0 mem0 E S M ms model _ _ _ cv Hd Hcv Cperm) as Hd1.
  assert (EQ1 : with_rgs S (carve_rgs cv) = mrg L Sp).
  { destruct S as [pc0 rg0 rgs0 fs0 nx0 rv0]. cbn [s_pc s_resv] in Hpc, Hrs. subst pc0 rv0.
    unfold with_rgs, mrg, L, Sp, nq_front, nq_rest. cbn [s_pc s_regs s_rgs s_facts s_next s_resv]. unfold front, rest. rewrite firstn_skipn. reflexivity. }
  rewrite EQ1 in Hd1.
  assert (EQb : bump (mrg L Sp) (s_next S + 66) = mrg Lb Sp) by reflexivity.
  pose proof (den_bump ASEGS LIMIT model0 mem0 E _ M ms model (s_next S + 66)%positive Hd1 ltac:(cbn [mrg s_next L nq_front]; lia)) as Hd2.
  rewrite EQb in Hd2.
  (* [comment removed for export] *)
  pose proof (po_inv _ _ _ _ HP0) as HI. unfold INV_A in HI. set (pz := pden E a) in *.
  pose proof (tg_pg_disj LIMIT model0 mem0 E S M ms model a mem0 Hd HP0) as Hdisj. fold pz in Hdisj.
  pose proof (az_geo pz mem0 HI) as G. pose proof (in_cls_rng c Hcin) as Hcr.
  destruct (cls_tbl c Hcin) as (Hszp & Hs8 & Hsz8 & Hnw & Hnm & Hmc).
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HRG & _ & HF0 & _).
  assert (Ej : uE E (p_j a c) = z_j pz c) by (symmetry; apply zn_pden).
  assert (Eca : uE E (p_ca a) = z_ca pz) by (symmetry; apply zn_pden).
  assert (Esb : uE E (p_sb a) = z_sb pz) by (symmetry; apply zn_pden).
  assert (Hjhi : z_j pz c + mc_tbl c / 2 + 1 <= 262144 / sz_tbl c).
  { pose proof (irange_sound E (s_facts S) (p_j a c) HF0) as X. fold (uE E (p_j a c)) in X. rewrite Ej in X. clear - X Cjb. lia. }
  destruct (iz_cls _ _ HI c Hcin) as [(_ & Z0 & HV & HSW)|(J1 & _)]; [|clear - J1 Hj0; lia].
  pose proof (iz_st _ _ HI) as HST.
  (* [comment removed for export] *)
  pose proof (irange_sound E (s_facts S) SPl HF0) as Rsp. fold (uE E SPl) in Rsp.
  pose proof (irange_sound E (s_facts S) szl HF0) as Rsz. fold (uE E szl) in Rsz.
  pose proof (irange_sound E (s_facts S) s6l HF0) as Rs6. fold (uE E s6l) in Rs6.
  assert (Hal : uE E SPl mod 16 = 0) by (pose proof (fact_implied_ok E _ _ HF0 Cmod) as X; cbn [fact_ok] in X; exact X).
  (* [comment removed for export] *)
  assert (Eqn : uE E (p_qn a) = z_qn pz) by (symmetry; apply zn_pden).
  assert (Eqb : uE E (p_qb a) = z_qb pz) by (symmetry; apply zn_pden).
  pose proof (irange_sound E (s_facts S) (p_qn a) HF0) as Rqn. fold (uE E (p_qn a)) in Rqn. rewrite Eqn in Rqn.
  destruct (iz_q _ _ HI) as [HQ0 _].
  (* [comment removed for export] *)
  assert (Rqf : fst (irange (s_facts S) (laddc szl 8192)) <= uE E szl + 8192 <= snd (irange (s_facts S) (laddc szl 8192))).
  { pose proof (irange_sound E (s_facts S) (laddc szl 8192) HF0) as X. fold (uE E (laddc szl 8192)) in X.
    assert (Y : snd (irange (s_facts S) szl) <= 2^40) by (first [exact Csz40 | apply Z.leb_le; exact Csz40]).
    rewrite uE_laddc_z in X by (pose proof (uE_range E szl) as U; clear - U Y Rsz; unfold two64 in *; lia). exact X. }
  cbv iota in Cnd.
  assert (Hqn0 : z_qn pz = 0 /\ z_qb pz = 0).
  { destruct HQ0 as (_ & _ & [(Q0 & Q1 & _)|(Q1 & _)]); [split; assumption | clear - Q1 Rqn Cqn0; lia]. }
  destruct Hqn0 as [Hqn0 Hqb0].
  set (sz := uE E szl) in *.
  assert (Hsz40 : 0 <= sz <= 2^40).
  { pose proof (uE_range E szl) as U1. fold sz in U1. clear - U1 Rsz Csz40. lia. }
  assert (Hmx : 0 <= uE E s6l < 2^62 /\ sz + 8192 <= uE E s6l).
  { pose proof (uE_range E s6l) as U2. pose proof (irange_sound E (s_facts S) (p_qb a) HF0) as Rqb. fold (uE E (p_qb a)) in Rqb. rewrite Eqb, Hqb0 in Rqb.
    clear - U2 Rqb Rsz Rs6 Cnd Cs6 Rqf. fold sz in Rsz, Rqf. lia. }
  (* [comment removed for export] *)
  assert (Hjlo : Z.ltb 0 (fst (irange (s_facts S) (p_j a c))) = false).
  { apply Z.ltb_ge. pose proof (irange_sound E (s_facts S) (p_j a c) HF0) as X. fold (uE E (p_j a c)) in X. rewrite Ej, Hj0 in X. clear - X. lia. }
  rewrite Hjlo in Cfu.
  apply andb_prop in Cfu as [Cfu Cfk2]. apply andb_prop in Cfu as [Cfu Cfk1]. apply andb_prop in Cfu as [Cfu Cenv]. apply andb_prop in Cfu as [Cfw Ctls].
  set (mr := ms_mem (restrict (Hof E M model) ms)) in *.
  (* [comment removed for export] *)
  assert (FWb : forallb (fun e => (Nat.leb 1 (snd (fst e)) && Nat.leb (snd (fst e)) 8 && Z.leb 0 (fst (fst e)) && Z.ltb (fst (fst e)) two64 &&
                                   Z.leb 0 (snd e) && Z.ltb (snd e) two64)%bool) FU_WORDS = true) by (vm_compute; reflexivity).
  assert (FW : forall e, In e FU_WORDS -> rd mr (fst (fst e)) (snd (fst e)) (snd e)).
  { intros e He. unfold fu_words_ok in Cfw. rewrite forallb_forall in Cfw, FWb. specialize (Cfw e He). specialize (FWb e He).
    apply andb_prop in FWb as [FWb B6]. apply andb_prop in FWb as [FWb B5]. apply andb_prop in FWb as [FWb B4]. apply andb_prop in FWb as [FWb B3].
    apply andb_prop in FWb as [B1 B2]. apply Nat.leb_le in B1, B2. apply Z.leb_le in B3, B5. apply Z.ltb_lt in B4, B6.
    apply (rdc_sound IMGP IMGP_ok E mr (s_rgs S)); [exact HRG | split; [exact B1 | exact B2] | split; [exact B3 | exact B4] | split; [exact B5 | exact B6] | exact Cfw]. }
  (* [comment removed for export] *)
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd1)) as (_ & _ & _ & Hregs1 & HRG1 & HDJ1 & _ & _).
  assert (HRGrest : Forall (rg_ok ASEGS E mr) rest).
  { cbn [mrg s_rgs L Sp nq_front nq_rest] in HRG1. apply Forall_app in HRG1. exact (proj2 HRG1). }
  (* [comment removed for export] *)
  unfold fu_tls_ok in Ctls. cbn [Sp nq_rest s_rgs s_regs] in Ctls.
  set (TPl := rget (s_regs S) (rk 4)) in *.
  destruct (rdw IMGP rest (lconst 941796) 4) as [Kl|] eqn:WK; [|discriminate].
  destruct (is_const Kl) as [K|] eqn:EK; [|discriminate]. destruct (is_const TPl) as [TP|] eqn:ETP; [|discriminate].
  destruct (rdw IMGP rest (laddc TPl (-88)) 8) as [TSDAl|] eqn:WT1; [|discriminate].
  destruct (is_const TSDAl) as [TSDA|] eqn:ETS; [|discriminate].
  destruct (rdw IMGP rest (laddc TSDAl (8 * K)) 8) as [PTl|] eqn:WT2; [|discriminate].
  destruct (rdw IMGP rest (laddc PTl 152) 8) as [Tl|] eqn:WT3; [|discriminate].
  apply andb_prop in Ctls as [Ctls Cgb]. apply andb_prop in Ctls as [Ctls Crgh].
  apply andb_prop in Ctls as [Ctls CT8]. apply andb_prop in Ctls as [Ctls CT7]. apply andb_prop in Ctls as [Ctls CT6]. apply andb_prop in Ctls as [Ctls CT5].
  apply andb_prop in Ctls as [Ctls CT4]. apply andb_prop in Ctls as [Ctls CT3]. apply andb_prop in Ctls as [CT1 CT2].
  apply Z.leb_le in CT1, CT2, CT5, CT6, CT7, CT8. apply lin_eqb_eq in CT3, CT4.
  assert (UK : uE E Kl = K) by (unfold uE; exact (is_const_u E _ _ EK)).
  assert (UTP : uE E TPl = TP) by (unfold uE; exact (is_const_u E _ _ ETP)).
  assert (UTS : uE E TSDAl = TSDA) by (unfold uE; exact (is_const_u E _ _ ETS)).
  set (PT := uE E PTl) in *.
  assert (Etg : uE E (p_tg a) = z_tg pz) by (symmetry; apply zn_pden).
  assert (Epg : uE E (p_pg a) = z_pg pz) by (symmetry; apply zn_pden).
  assert (UT : uE E Tl = z_tg pz) by (rewrite CT4; exact Etg).
  pose proof (rdw_sound IMGP IMGP_ok E mr rest _ 4 _ HRGrest ltac:(lia) WK) as Itls2. rewrite uE_lc, UK in Itls2 by lia.
  pose proof (rdw_sound IMGP IMGP_ok E mr rest _ 8 _ HRGrest ltac:(lia) WT1) as Itls3.
  rewrite uE_laddc_z, UTP, UTS in Itls3 by (rewrite UTP; unfold two64; clear - CT5 CT6; lia).
  pose proof (rdw_sound IMGP IMGP_ok E mr rest _ 8 _ HRGrest ltac:(lia) WT2) as Itls4.
  rewrite uE_laddc_z, UTS in Itls4 by (rewrite UTS; unfold two64; clear - CT1 CT2 CT7 CT8; lia). fold PT in Itls4.
  pose proof (rdw_sound IMGP IMGP_ok E mr rest _ 8 _ HRGrest ltac:(lia) WT3) as Itls5.
  destruct (rdw_in IMGP E mr rest _ 8 _ HRGrest ltac:(lia) WT3) as (Rpt & HRpt & Ppt1 & Ppt2).
  (* [comment removed for export] *)
  pose proof (dn_own _ _ _ _ _ _ _ _ _ Hd1) as Hown1.
  assert (Hcell : forall x, 0 <= x < 2^64 -> FPmax pz x -> ~ alloc_part pz x -> pri_foot_z pz x -> mr (wa x) = mem0 (wa x) /\ Hof E M model (wa x) = false).
  { intros x Hx F2 F3 F1. destruct (po_own _ _ _ _ HP0 x Hx F1) as (p & Hp & Hpw). pose proof (Hown1 p Hp x Hpw) as [Hv Hm]. split; [|exact Hv].
    unfold mr. cbn [restrict ms_mem]. unfold mrestrict. unfold wa. rewrite Hv. apply Hm.
    exact (pri_outside_den LIMIT model0 mem0 E (mrg L Sp) M ms model a mem0 jP jT Hd1 HP0 HjP HjT Csep x ltac:(unfold two64; lia) F2 F3). }
  set (CA := z_ca pz) in *. set (SB := z_sb pz) in *. set (SH := z_sh pz) in *. set (TT := z_tg pz) in *.
  set (RIv := SB + 137438953472 + 128 * c). set (RBv := SB + 4294967296 * c). set (FAv := SB + 4294967296 * c + 3758096384).
  assert (B0 : 4096 <= TT /\ CA = TT + 208 /\ CA + 3888 <= 2^47 /\ z_pg pz <= SB /\ SB + 137438953472 + 4096 <= z_pg pz + 137439023104 /\
               z_pg pz + 137439023104 <= 2^47 /\ 17594333495296 <= z_pg pz /\ 17594333495296 <= SB) by (clear - G; unfold CA, SB, TT; lia).
  assert (Hvf : forall x, (CA - 128 <= x < CA + 2592 \/ SB + 137438953472 <= x < SB + 137438953472 + 4096 \/
                           RBv <= x < RBv + 262144 \/ FAv <= x < FAv + 262144 \/
                           SH + 536870912 * c <= x < SH + 536870912 * c + 32768 \/
                           SH + 536870912 * c + 469762048 <= x < SH + 536870912 * c + 469762048 + 32768) ->
                          FPmax pz x /\ ~ alloc_part pz x /\ 0 <= x < 2^47) by (intros x Hx; exact (virgin_fp pz mem0 HI Hdisj c x Hcin Hj0 Hx)).
  (* [comment removed for export] *)
  assert (Hmr_foot : forall x, (CA - 128 <= x < CA + 2592 \/ SB + 137438953472 <= x < SB + 137438953472 + 4096 \/
                           SH + 536870912 * c <= x < SH + 536870912 * c + 32768 \/
                           SH + 536870912 * c + 469762048 <= x < SH + 536870912 * c + 469762048 + 32768) -> mr (wa x) = mem0 (wa x)).
  { intros x Hx. destruct (Hvf x ltac:(clear - Hx; lia)) as (F2 & F3 & F4).
    apply (Hcell x ltac:(clear - F4; lia) F2 F3). unfold pri_foot_z. fold CA SB SH.
    destruct Hx as [Hx|[Hx|Hx]]; [left; exact Hx | right; left; exact Hx |]. right. right. right. exists c. split; [exact Hcin|]. right. right. exact Hx. }
  (* [comment removed for export] *)
  destruct HV as [Vcnt Vic Vri Vwc Vwri]. destruct HSW as [Wsh Wshf]. destruct HST as ((st & Hst & Rst) & (st2 & Hst2 & Rst2) & Wst).
  fold CA SB in Vcnt, Vic, Vri, Vwc, Vwri, Rst, Rst2, Wst. fold SH in Wsh, Wshf.
  assert (Icnt : rd mr (CA + 80 * c) 4 0).
  { apply (rd_frame mem0); [clear - B0 Hcr; lia | cbn; clear - B0 Hcr; lia | intros x Hx; cbn in Hx; apply Hmr_foot; left; clear - Hx Hcr; lia | exact Vcnt]. }
  assert (Ist : rd mr (CA + 2576) 8 st).
  { apply (rd_frame mem0); [clear - B0; lia | cbn; clear - B0; lia | intros x Hx; cbn in Hx; apply Hmr_foot; left; clear - Hx; lia | exact Rst]. }
  assert (Ist2 : rd mr (CA + 2584) 8 st2).
  { apply (rd_frame mem0); [clear - B0; lia | cbn; clear - B0; lia | intros x Hx; cbn in Hx; apply Hmr_foot; left; clear - Hx; lia | exact Rst2]. }
  assert (Iwc : wr mr CA 2592).
  { apply (wr_frame mem0); [clear - B0; lia | clear - B0; lia | intros x Hx; apply Hmr_foot; left; clear - Hx; lia |].
    exact (wr_sub mem0 (CA - 128) 2720 CA 2592 (iz_wc _ _ HI) ltac:(clear; lia) ltac:(clear; lia)). }
  assert (Iri : forall i, 0 <= i < 16 -> rd mr (RIv + 8 * i) 8 0).
  { intros i Hi. apply (rd_frame mem0); [unfold RIv; clear - B0 Hcr Hi; lia | cbn; unfold RIv; clear - B0 Hcr Hi; lia | | exact (Vri i Hi)].
    intros x Hx. cbn in Hx. apply Hmr_foot. right. left. unfold RIv in Hx. clear - Hx Hcr Hi. lia. }
  assert (Iwri : wr mr RIv 128).
  { apply (wr_frame mem0); [unfold RIv; clear - B0 Hcr; lia | unfold RIv; clear - B0 Hcr; lia | | exact Vwri].
    intros x Hx. apply Hmr_foot. right. left. unfold RIv in Hx. clear - Hx Hcr. lia. }
  assert (S1 : 2199291686912 + 2147450880 <= SH /\ SH + 17179869184 <= z_pg pz) by (clear - G; unfold SH; lia).
  assert (Iwsh : wr mr (SH + 536870912 * c) 32768).
  { apply (wr_frame mem0); [clear - S1 Hcr; lia | clear - S1 B0 Hcr; lia | intros x Hx; apply Hmr_foot; right; right; left; exact Hx | exact Wsh]. }
  assert (Iwshf : wr mr (SH + 536870912 * c + 469762048) 32768).
  { apply (wr_frame mem0); [clear - S1 Hcr; lia | clear - S1 B0 Hcr; lia | intros x Hx; apply Hmr_foot; right; right; right; exact Hx | exact Wshf]. }
  (* [comment removed for export] *)
  destruct (rg_hdr_b_sound _ _ _ _ Cwin) as (cw & Pw). destruct (ro_b_sound _ Cro) as (zro & Hzro & Pro).
  destruct (rg_hdr_b_sound _ _ _ _ Cst) as (cs & Pst).
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd1)) as Hd10.
  pose proof (mrg_rg0 E L Sp _ 0%nat _ Hd10 Pw) as Rw. pose proof (mrg_rg0 E L Sp _ 1%nat _ Hd10 Pro) as Rro.
  pose proof (mrg_rg0 E L Sp _ 2%nat _ Hd10 Pst) as Rst0. fold mr in Rw, Rro, Rst0.
  set (SP := uE E SPl) in *.
  assert (HSPr : 2^46 + 8192 <= SP <= 2^47) by (clear - Rsp Csplo Csphi; lia).
  assert (Ebw : bv_unsigned (lden E (laddc SPl (-2064))) = SP - 2064) by (rewrite lden_laddc; fold (uE E SPl); fold SP; rewrite u_small64; unfold two64; clear - HSPr; lia).
  (* [comment removed for export] *)
  remember (SP - 16) as SPq eqn:ESPq.
  assert (HSTK16 : stk_ok SEGS mr (wa (SPq + 16)) 2064).
  { replace (SPq + 16) with SP by (clear - ESPq; lia).
    intros a0 k Ha Hk'. rewrite u_wa_small in Ha, Hk' by (clear - HSPr; lia). apply store_ok_of_all; [pose proof (bv_unsigned_in_range _ a0); clear - Ha Hk' HSPr H; lia|].
    intros x Hx. pose proof (bv_unsigned_in_range _ x) as Rx.
    destruct (rg_rw_pt _ _ _ (bv_unsigned x) Rw eq_refl) as [_ W].
    { cbn [rg_base]. rewrite Ebw. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). clear - Ha Hk' Hx. lia. }
    rewrite Z_to_bv_bv_unsigned in W. exact W. }
  assert (HSTK : stk_ok SEGS mr (wa SPq) 2048).
  { intros a0 k Ha Hk'. apply HSTK16; rewrite u_wa_small in * by (clear - HSPr ESPq; lia); [clear - Ha; lia | clear - Hk'; lia]. }
  assert (HIMG : forall i, 65536 <= i < 143360 -> mr (Z_to_bv 64 i) = None) by exact (ro_none_z _ _ _ Hzro Rro).
  destruct (rw_words16 E mr _ (TT + 2872) Rst0 eq_refl) as ((mm1 & Hmm1 & Imm1) & (mm2 & Hmm2 & Imm2) & Iwt).
  { cbn [rg_base]. rewrite uE_laddc_z by (rewrite Etg; fold TT; unfold two64; clear - B0; lia). rewrite Etg. reflexivity. }
  { unfold rsz. cbn [rg_size]. rewrite lden_lconst. apply u_small64. unfold two64. lia. }
  { clear - B0. lia. } { clear - B0. lia. }
  replace (TT + 2872 + 8) with (TT + 2880) in Imm2 by ring.
  (* [comment removed for export] *)
  assert (HPTrg : exists Rp, In Rp rest /\ uE E (rg_base Rp) <= PT /\ PT + 160 <= uE E (rg_base Rp) + rsz E Rp).
  { unfold rg_has in Crgh. rewrite existsb_l_eq in Crgh. apply existsb_exists in Crgh as (Rp & HRp & Hc0).
    destruct (lin_off PTl (rg_base Rp)) as [o0|] eqn:Hl; [|discriminate]. destruct (is_const (rg_size Rp)) as [z0|] eqn:Hz0; [|discriminate].
    apply andb_prop in Hc0 as [C1 C2]. apply Z.leb_le in C1, C2. rewrite Forall_forall in HRGrest. pose proof (HRGrest Rp HRp) as HRp0.
    assert (Ez0 : rsz E Rp = z0) by (unfold rsz; exact (is_const_u E _ _ Hz0)).
    pose proof (OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcRdw.lin_off_u E mr PTl Rp o0 160 HRp0 Hl C1 ltac:(rewrite Ez0; exact C2) ltac:(lia)) as Ea.
    exists Rp. split; [exact HRp|]. fold PT in Ea. rewrite Ea, Ez0. clear - C1 C2. lia. }
  assert (HPTband : 1 <= PT /\ PT + 160 + 4320 <= SP).
  { rewrite existsb_l_eq in Cgb. apply existsb_exists in Cgb as (g & Hg & Hc0). cbn [Sp nq_rest s_facts] in Hc0.
    apply andb_prop in Hc0 as [C1 C2]. apply lin_eqb_eq in C1. apply Z.leb_le in C2.
    pose proof (band_hi LIMIT model0 mem0 E S M ms model SPl g Hd Cband Hg) as BG. fold (uE E SPl) in BG. fold SP in BG. rewrite C1 in BG. fold PT in BG.
    pose proof (gsz_bounds E (s_facts S) g HF0) as GB. pose proof (dn_gsh _ _ _ _ _ _ _ _ _ Hd) as Hgs. rewrite Forall_forall in Hgs.
    destruct (Hgs g Hg) as (_ & _ & _ & _ & G5). rewrite C1 in G5. fold PT in G5. clear - BG GB C2 G5. lia. }
  assert (EPT152 : uE E (laddc PTl 152) = PT + 152) by (apply uE_laddc_z; fold PT; unfold two64; clear - HPTband HSPr; lia).
  rewrite EPT152, UT in Itls5.
  (* [comment removed for export] *)
  assert (Hvout : forall x, (CA - 128 <= x < CA + 2592 \/ SB + 137438953472 <= x < SB + 137438953472 + 4096 \/
                           RBv <= x < RBv + 262144 \/ FAv <= x < FAv + 262144 \/
                           SH + 536870912 * c <= x < SH + 536870912 * c + 32768 \/
                           SH + 536870912 * c + 469762048 <= x < SH + 536870912 * c + 469762048 + 32768) ->
                          outside E (s_rgs (mrg L Sp)) (Z_to_bv 64 x)).
  { intros x Hx. destruct (Hvf x Hx) as (F2 & F3 & F4).
    exact (pri_outside_den LIMIT model0 mem0 E (mrg L Sp) M ms model a mem0 jP jT Hd1 HP0 HjP HjT Csep x ltac:(unfold two64; clear - F4; lia) F2 F3). }
  (* [comment removed for export] *)
  destruct HPTrg as (Rp & HRp & Pp1 & Pp2).
  assert (HPTv : forall w, PT <= w < PT + 160 -> ~ (CA - 128 <= w < CA + 2592 \/ SB + 137438953472 <= w < SB + 137438953472 + 4096 \/
                           RBv <= w < RBv + 262144 \/ FAv <= w < FAv + 262144 \/
                           SH + 536870912 * c <= w < SH + 536870912 * c + 32768 \/
                           SH + 536870912 * c + 469762048 <= w < SH + 536870912 * c + 469762048 + 32768)).
  { intros w Hw Hv. pose proof (Hvout w Hv) as Hou. unfold outside in Hou. rewrite Forall_forall in Hou.
    specialize (Hou Rp ltac:(cbn [mrg s_rgs L Sp nq_front nq_rest]; apply in_or_app; right; exact HRp)).
    destruct (Hvf w Hv) as (_ & _ & F4). rewrite u_small64 in Hou by (unfold two64; clear - F4; lia). unfold uE in Pp1, Pp2. clear - Hou Hw Pp1 Pp2. lia. }
  (* [comment removed for export] *)
  set (regs := ms_regs ms) in *.
  assert (R2 : getr regs (Z_to_bv 5 2) = wa SP).
  { change regs with (ms_regs (restrict (Hof E M model) ms)). rewrite (mrg_reg0 E L Sp _ (Z_to_bv 5 2) _ Hd10 eq_refl). unfold wa, SP, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (Ecb : uE E (l_cb a) = CA - 128).
  { unfold l_cb. rewrite uE_laddc_z by (rewrite Eca; fold CA; unfold two64; clear - B0; lia). rewrite Eca. reflexivity. }
  assert (Rg1 : getr regs (Z_to_bv 5 1) = wa 278036).
  { change regs with (ms_regs (restrict (Hof E M model) ms)). rewrite (mrg_reg0 E L Sp _ (Z_to_bv 5 1) _ Hd10 Cra). rewrite lden_lconst. reflexivity. }
  assert (Rg9 : getr regs (Z_to_bv 5 9) = wa (CA - 128)).
  { change regs with (ms_regs (restrict (Hof E M model) ms)). rewrite (mrg_reg0 E L Sp _ (Z_to_bv 5 9) _ Hd10 Cs1). rewrite <- Ecb. unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R10 : getr regs (Z_to_bv 5 10) = wa (CA - 128)).
  { change regs with (ms_regs (restrict (Hof E M model) ms)). rewrite (mrg_reg0 E L Sp _ (Z_to_bv 5 10) _ Hd10 Ca0). rewrite <- Ecb. unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R11 : getr regs (Z_to_bv 5 11) = wa CA).
  { change regs with (ms_regs (restrict (Hof E M model) ms)). rewrite (mrg_reg0 E L Sp _ (Z_to_bv 5 11) _ Hd10 Ca1). unfold wa. rewrite <- Eca. unfold uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  set (mp := bv_unsigned (getr regs (Z_to_bv 5 13))).
  assert (Rg13 : getr regs (Z_to_bv 5 13) = wa mp) by (unfold mp, wa; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hmp : 0 <= mp < 2^64) by (pose proof (bv_unsigned_in_range _ (getr regs (Z_to_bv 5 13))) as U3; fold mp in U3; change (bv_modulus 64) with (2^64) in U3; exact U3).
  assert (Rg14 : getr regs (Z_to_bv 5 14) = wa sz).
  { change regs with (ms_regs (restrict (Hof E M model) ms)). rewrite (mrg_reg0 E L Sp _ (Z_to_bv 5 14) _ Hd10 eq_refl). unfold wa, sz, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  set (mx := uE E s6l) in *.
  assert (Rg22 : getr regs (Z_to_bv 5 22) = wa mx).
  { change regs with (ms_regs (restrict (Hof E M model) ms)). rewrite (mrg_reg0 E L Sp _ (Z_to_bv 5 22) _ Hd10 eq_refl). unfold wa, mx, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R4 : getr regs (Z_to_bv 5 4) = wa TP).
  { change regs with (ms_regs (restrict (Hof E M model) ms)). rewrite (mrg_reg0 E L Sp _ (Z_to_bv 5 4) _ Hd10 eq_refl). fold TPl. unfold wa. rewrite <- UTP. unfold uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  (* [comment removed for export] *)
  destruct (po_gp _ _ _ _ HP0) as (kp & Hgp). destruct (po_gt _ _ _ _ HP0) as (kt & Hgt).
  pose proof (band_hi LIMIT model0 mem0 E S M ms model SPl _ Hd Cband Hgp) as BP.
  pose proof (band_hi LIMIT model0 mem0 E S M ms model SPl _ Hd Cband Hgt) as BT.
  unfold gsz in BP, BT. cbn [fst snd] in BP, BT. unfold PG_SIZE, TG_SIZE in BP, BT. rewrite uE_lc in BP, BT by lia.
  rewrite Epg in BP. rewrite Etg in BT. fold (uE E SPl) in BP, BT. fold SP TT in BP, BT.
  pose proof (iz_ca _ _ HI) as (Pca & Aca & _). fold pz CA in Pca, Aca.
  assert (T1 : CA + 2592 <= z_pg pz \/ z_pg pz + 137439023104 <= CA - 128) by (clear - Hdisj B0; unfold PG_SIZE in Hdisj; fold TT in Hdisj; lia).
  assert (HCA' : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SPq - 2048) by (split; [exact Pca|]; split; [exact Aca|]; clear - B0 BT ESPq; lia).
  assert (HSB' : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SPq - 2048).
  { pose proof (proj2 (iz_sb _ _ HI)) as X2. fold pz SB in X2. clear - B0 BP X2 ESPq. split; [lia|]. split; [exact X2 | lia]. }
  assert (HSEP' : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) by (clear - T1 B0; lia).
  assert (HSEPQ : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA - 128) by (clear - T1 B0; lia).
  set (SHv := Z.shiftr (SB + 4294967296 * c) 3 + 2147450880). set (SHFv := Z.shiftr (SB + 4294967296 * c + 3758096384) 3 + 2147450880).
  assert (ESH : SHv = SH + 536870912 * c /\ SHFv = SH + 536870912 * c + 469762048).
  { unfold SHv, SHFv. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. destruct G as (_ & _ & _ & _ & _ & Gm8 & Gsh & _). fold SB SH in Gm8, Gsh.
    pose proof (Z.div_mod SB 8 ltac:(lia)) as Ed. rewrite Gm8, Z.add_0_r in Ed. rewrite Gsh.
    replace (SB + 4294967296 * c) with ((SB / 8 + 536870912 * c) * 8) by (clear - Ed; lia).
    replace ((SB / 8 + 536870912 * c) * 8 + 3758096384) with ((SB / 8 + 536870912 * c + 469762048) * 8) by (clear; lia). rewrite !Z.div_mul by (clear; lia). clear. lia. }
  destruct ESH as [ESHv ESHFv].
  (* [comment removed for export] *)
  assert (PTsep : forall b m, 0 < m -> (forall w, b <= w < b + m -> CA - 128 <= w < CA + 2592 \/ SB + 137438953472 <= w < SB + 137438953472 + 4096 \/
                           RBv <= w < RBv + 262144 \/ FAv <= w < FAv + 262144 \/
                           SH + 536870912 * c <= w < SH + 536870912 * c + 32768 \/
                           SH + 536870912 * c + 469762048 <= w < SH + 536870912 * c + 469762048 + 32768) -> PT + 160 <= b \/ b + m <= PT).
  { intros b m Hm Hb. apply (iv_apart PT 160 b m ltac:(lia) Hm). intros w Hw Hwb. exact (HPTv w Hw (Hb w Hwb)). }
  assert (Hnsh : TT + 4096 <= 2147446784 \/ 17594333495296 <= TT) by (clear - G; unfold TT; lia).
  assert (S3 : SH + 17179869184 <= 17594333495296) by (clear - G; unfold SH; lia).
  assert (HO : objs_ok_p (SPq - 2048) TT RIv TP TSDA PT).
  { unfold objs_ok_p, t_place. destruct (PTsep (SB + 137438953472) 4096 ltac:(lia) ltac:(intros w Hw; right; left; exact Hw)) as [X|X];
      unfold RIv; clear - HSPr ESPq B0 BT BP Pca T1 Hcr CT5 CT6 CT7 CT8 CT1 CT2 HPTband X; lia. }
  assert (HSHs : shsep TT RIv TP TSDA PT SHv).
  { unfold shsep. rewrite ESHv.
    destruct (PTsep (SH + 536870912 * c) 32768 ltac:(lia) ltac:(intros w Hw; do 4 right; left; exact Hw)) as [X|X];
      unfold RIv; clear - S1 S3 Hnsh B0 Hcr CT5 CT6 CT7 CT8 CT1 CT2 X; lia. }
  assert (HSHF : shsep TT RIv TP TSDA PT SHFv).
  { unfold shsep. rewrite ESHFv.
    destruct (PTsep (SH + 536870912 * c + 469762048) 32768 ltac:(lia) ltac:(intros w Hw; do 5 right; exact Hw)) as [X|X];
      unfold RIv; clear - S1 S3 Hnsh B0 Hcr CT5 CT6 CT7 CT8 CT1 CT2 X; lia. }
  (* [comment removed for export] *)
  assert (HPTst : PT + 160 <= TT + 2872 \/ TT + 2888 <= PT).
  { destruct (In_nth_error _ _ HRp) as (ip & Hip).
    assert (Hlf : length front = 3%nat).
    { assert (A1 : (length front <= 3)%nat) by (unfold front; rewrite length_firstn; apply Nat.le_min_l).
      assert (A2 : (2 < length front)%nat) by (apply nth_error_Some; rewrite Pst; discriminate). clear - A1 A2. lia. }
    assert (N1 : nth_error (s_rgs (mrg L Sp)) (3 + ip) = Some Rp).
    { cbn [mrg s_rgs L Sp nq_front nq_rest]. rewrite nth_error_app2 by (rewrite Hlf; clear; lia). rewrite Hlf. replace (3 + ip - 3)%nat with ip by (clear; lia). exact Hip. }
    assert (N2 : nth_error (s_rgs (mrg L Sp)) 2 = Some (RG (laddc (p_tg a) 2872) (lconst 16) RW cs)).
    { cbn [mrg s_rgs L Sp nq_front nq_rest]. rewrite nth_error_app1 by (rewrite Hlf; clear; lia). exact Pst. }
    pose proof (rgs_disj_nth E _ (3 + ip)%nat 2%nat _ _ HDJ1 ltac:(clear; lia) N1 N2) as Hdj. unfold rg_disj in Hdj. cbv zeta in Hdj. cbn [rg_base] in Hdj.
    unfold rsz in Hdj at 2. cbn [rg_size] in Hdj. rewrite lden_lconst, (u_small64 16) in Hdj by (unfold two64; lia).
    fold (uE E (laddc (p_tg a) 2872)) in Hdj. rewrite uE_laddc_z in Hdj by (rewrite Etg; fold TT; unfold two64; clear - B0; lia). rewrite Etg in Hdj. fold TT in Hdj.
    fold (uE E (rg_base Rp)) in Hdj. clear - Hdj Pp1 Pp2. lia. }
  (* [comment removed for export] *)
  assert (HENV : forall x, qENVC TP K TSDA PT x -> ~ qCHC CA c SB SPq TT x).
  { intros x He Hc0. unfold qENVC in He. unfold qCHC in Hc0. cbv zeta in Hc0. fold SHv SHFv in Hc0. rewrite ESHv, ESHFv in Hc0.
    assert (Hx3 : (65536 <= x < 6537216) \/ PT + 152 <= x < PT + 160) by (clear - He CT1 CT2 CT5 CT6 CT7 CT8; lia). clear He.
    destruct Hx3 as [Hx3|Hx3].
    - unfold RBv, FAv in Hc0. clear - Hc0 Hx3 HSPr ESPq Pca B0 S1 Hcr. lia.
    - assert (Hpt : PT <= x < PT + 160) by (clear - Hx3; lia).
      destruct Hc0 as [Hc0|[Hc0|[Hc0|[Hc0|Hc0]]]].
      + clear - Hc0 Hx3 HPTband ESPq. lia.
      + apply (HPTv x Hpt). left. clear - Hc0. lia.
      + apply (HPTv x Hpt). right. left. clear - Hc0 Hcr. lia.
      + clear - Hc0 Hx3 HPTst. lia.
      + apply (HPTv x Hpt). right. right. unfold RBv, FAv. clear - Hc0. lia. }
  (* [comment removed for export] *)
  unfold sb_words_ok in Csbw. destruct (rdw IMGP (s_rgs S) (lconst 929848) 8) as [l1|] eqn:W1; [|discriminate].
  destruct (rdw IMGP (s_rgs S) (lconst 929864) 8) as [l2|] eqn:W2; [|discriminate].
  apply andb_prop in Csbw as [Q1 Q2]. apply lin_eqb_eq in Q1, Q2. subst l1 l2.
  pose proof (rdw_sound IMGP IMGP_ok E _ (s_rgs S) (lconst 929848) 8 _ HRG ltac:(lia) W1) as RSB.
  pose proof (rdw_sound IMGP IMGP_ok E _ (s_rgs S) (lconst 929864) 8 _ HRG ltac:(lia) W2) as RRIB.
  rewrite uE_lc in RSB, RRIB by lia. rewrite Esb in RSB.
  assert (Erip : uE E (l_rip a) = z_sb pz + 137438953472).
  { unfold l_rip. rewrite uE_laddc2 by (rewrite ?Esb; unfold two64; clear - B0; fold SB; lia). rewrite Esb. reflexivity. }
  rewrite Erip in RRIB.
  fold SB in RSB, RRIB.
  (* [comment removed for export] *)
  set (fx1 := mkFP (ms_fregs ms) (ms_fcsr ms)).
  (* [comment removed for export] *)
  assert (Rq0m : rd mem0 (CA - 128) 8 0 /\ rd mem0 (CA - 128 + 24) 8 0).
  { destruct HQ0 as (_ & Rb & [(_ & _ & R0)|(Q1 & _)]); [|clear - Q1 Hqn0; lia]. rewrite Hqb0 in Rb. split; assumption. }
  assert (Rq0 : rd mr (CA - 128) 8 0).
  { apply (rd_frame mem0); [clear - B0; lia | cbn; clear - B0; lia | intros x Hx; cbn in Hx; apply Hmr_foot; left; clear - Hx; lia | exact (proj1 Rq0m)]. }
  assert (Rqb : rd mr (CA - 128 + 24) 8 0).
  { apply (rd_frame mem0); [clear - B0; lia | cbn; clear - B0; lia | intros x Hx; cbn in Hx; apply Hmr_foot; left; clear - Hx; lia | exact (proj2 Rq0m)]. }
  assert (Hwq : wr mr (CA - 128) 32).
  { apply (wr_frame mem0); [clear - B0; lia | clear - B0; lia | intros x Hx; apply Hmr_foot; left; clear - Hx; lia |].
    exact (wr_sub mem0 (CA - 128) 2720 (CA - 128) 32 (iz_wc _ _ HI) ltac:(clear; lia) ltac:(clear; lia)). }
  assert (HSPa : 2^46 + 4096 <= SPq /\ SPq + 16 <= 2^47 /\ SPq mod 16 = 0) by (clear - HSPr ESPq Hal; lia).
  assert (HSPp : 2^46 + 4096 <= SPq <= 2^47 /\ SPq mod 16 = 0) by (clear - HSPr ESPq Hal; lia).
  assert (HSP16 : SPq + 16 <= 2^47) by (clear - HSPr ESPq; lia).
  assert (HfmA : 0 <= sz <= 2^40 /\ 0 <= mp < 2^64) by (split; [exact Hsz40 | exact Hmp]).
  assert (Hfm : 0 <= sz <= 2^40 /\ 0 <= mp < 2^64 /\ 0 <= mx < 2^62 /\ sz + 8192 <= mx) by (clear - Hsz40 Hmp Hmx; fold mx in Hmx; lia).
  assert (R1b : getr regs (1%bv : reg) = wa 278036) by (replace (1%bv : reg) with (Z_to_bv 5 1) by (apply bv_eq; reflexivity); exact Rg1).
  assert (R2b : getr regs (2%bv : reg) = wa (SPq + 16)).
  { replace (2%bv : reg) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity). replace (SPq + 16) with SP by (clear - ESPq; lia). exact R2. }
  assert (R4b : getr regs (4%bv : reg) = wa TP) by (replace (4%bv : reg) with (Z_to_bv 5 4) by (apply bv_eq; reflexivity); exact R4).
  assert (R9b : getr regs (9%bv : reg) = wa (CA - 128)) by (replace (9%bv : reg) with (Z_to_bv 5 9) by (apply bv_eq; reflexivity); exact Rg9).
  assert (R10b : getr regs (10%bv : reg) = wa (CA - 128)) by (replace (10%bv : reg) with (Z_to_bv 5 10) by (apply bv_eq; reflexivity); exact R10).
  assert (R11b : getr regs (11%bv : reg) = wa CA) by (replace (11%bv : reg) with (Z_to_bv 5 11) by (apply bv_eq; reflexivity); exact R11).
  assert (R13b : getr regs (13%bv : reg) = wa mp) by (replace (13%bv : reg) with (Z_to_bv 5 13) by (apply bv_eq; reflexivity); exact Rg13).
  assert (R14b : getr regs (14%bv : reg) = wa sz) by (replace (14%bv : reg) with (Z_to_bv 5 14) by (apply bv_eq; reflexivity); exact Rg14).
  assert (R22b : getr regs (22%bv : reg) = wa mx) by (replace (22%bv : reg) with (Z_to_bv 5 22) by (apply bv_eq; reflexivity); exact Rg22).
  assert (HstA : exists R1 mA, msteps SEGS (@mkst fx1 regs (wa 0x43e20) mr (ms_rom ms)) (@mkst fx1 R1 (wa 0x73c38) mA (ms_rom ms)) /\
            EC R1 RBv /\ getr R1 (Z_to_bv 5 (Z.of_nat 1)) = wa 481784 /\ getr R1 (Z_to_bv 5 (Z.of_nat 2)) = wa (SPq - 400) /\
            getr R1 (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R1 (Z_to_bv 5 (Z.of_nat 21)) = wa (sz_tbl c) /\ getr R1 (Z_to_bv 5 (Z.of_nat 22)) = wa 929816 /\
            (forall k, In k [3; 4]%nat -> getr R1 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
            qMA_OK mr mA regs SPq CA c RIv RBv FAv (CA - 128) sz mp /\
            ((forall i, 1 <= i <= 31 -> rd mA (CA + 80 * i + 4) 4 (mc_tbl i) /\ rd mA (CA + 80 * i + 8) 8 (sz_tbl i)) \/
             (forall x, CA <= x < CA + 2592 -> mA (wa x) = mr (wa x))) /\
            (forall x, 0 <= x < 2^64 -> ~ (SPq - 2048 <= x < SPq + 16) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= x < CA + 80 * i + 16)) ->
               ~ (RIv <= x < RIv + 8) -> mA (wa x) = mr (wa x))).
  { pose proof (FW (929856, 4%nat, 4294967295) (nth_error_In FU_WORDS 5 eq_refl)) as W1'. cbn [fst snd] in W1'.
    pose proof (FW (929872, 1%nat, 0) (nth_error_In FU_WORDS 6 eq_refl)) as W2'. cbn [fst snd] in W2'.
    pose proof (FW (910448, 8%nat, 1532192) (nth_error_In FU_WORDS 0 eq_refl)) as W3'. cbn [fst snd] in W3'.
    pose proof (FW (1532192, 8%nat, 4096) (nth_error_In FU_WORDS 1 eq_refl)) as W4'. cbn [fst snd] in W4'.
    pose proof (FW (910464, 8%nat, 1540520) (nth_error_In FU_WORDS 2 eq_refl)) as W5'. cbn [fst snd] in W5'.
    pose proof (FW (1540780, 1%nat, 0) (nth_error_In FU_WORDS 4 eq_refl)) as W6'. cbn [fst snd] in W6'.
    destruct Vic as [(Vmc & sz0 & Hsz0 & Vsz)|(Vmc & Vsz)].
    - (* [comment removed for export] *)
      assert (Imc : rd mr (CA + 80 * c + 4) 4 0).
      { apply (rd_frame mem0); [clear - B0 Hcr; lia | cbn; clear - B0 Hcr; lia | intros x Hx; cbn in Hx; apply Hmr_foot; left; clear - Hx Hcr; lia | exact Vmc]. }
      assert (Isz : rd mr (CA + 80 * c + 8) 8 sz0).
      { apply (rd_frame mem0); [clear - B0 Hcr; lia | cbn; clear - B0 Hcr; lia | intros x Hx; cbn in Hx; apply Hmr_foot; left; clear - Hx Hcr; lia | exact Vsz]. }
      destruct (@qstageA fx1 (ms_rom ms) mr regs (CA - 128) CA c SB SPq sz0 st sz mp Hc24 R2b HSPa HSTK16 R10b R11b R13b R14b eq_refl HfmA Rq0 HCA' HSB' HSEP' (conj Hsz0 Hst)
                  Icnt Imc Isz Ist Iwc Iri Iwri RSB RRIB W1' W2' W3' W4' W5' W6') as (R1 & mA & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
      exists R1, mA. repeat (split; [assumption|]). split; [left; exact A10 | exact A11].
    - (* [comment removed for export] *)
      assert (Imc : rd mr (CA + 80 * c + 4) 4 (mc_tbl c)).
      { apply (rd_frame mem0); [clear - B0 Hcr; lia | cbn; clear - B0 Hcr; lia | intros x Hx; cbn in Hx; apply Hmr_foot; left; clear - Hx Hcr; lia | exact Vmc]. }
      assert (Isz : rd mr (CA + 80 * c + 8) 8 (sz_tbl c)).
      { apply (rd_frame mem0); [clear - B0 Hcr; lia | cbn; clear - B0 Hcr; lia | intros x Hx; cbn in Hx; apply Hmr_foot; left; clear - Hx Hcr; lia | exact Vsz]. }
      destruct (@qstageA' fx1 (ms_rom ms) mr regs (CA - 128) CA c SB SPq st sz mp Hc24 R2b HSPa HSTK16 R10b R11b R13b R14b eq_refl HfmA Rq0 HCA' HSB' HSEP' Hst
                  Icnt Imc Isz Ist Iwc Iri Iwri RSB RRIB W1' W2' W3' W4' W5' W6') as (R1 & mA & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A11).
      exists R1, mA. repeat (split; [assumption|]). split.
      + right. intros x Hx. apply A11; [clear - Hx B0; lia | clear - Hx HCA'; lia | unfold RIv; clear - Hx HSEP' Hcr; lia].
      + intros x Hx Hw _ Hri. exact (A11 x Hx Hw Hri). }
  destruct HstA as (R1 & mA & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
  (* [comment removed for export] *)
  assert (Hvown : forall x, (CA - 128 <= x < CA + 2592 \/ SB + 137438953472 <= x < SB + 137438953472 + 4096 \/
                           SH + 536870912 * c <= x < SH + 536870912 * c + 32768 \/
                           SH + 536870912 * c + 469762048 <= x < SH + 536870912 * c + 469762048 + 32768) ->
                          own_pt E M x /\ outside E (s_rgs (mrg L Sp)) (wa x) /\ ~ frz_pt E M x).
  { intros x Hx. destruct (Hvf x ltac:(clear - Hx; lia)) as (F2 & F3 & F4).
    assert (F1 : pri_foot_z pz x).
    { unfold pri_foot_z. fold CA SB SH. destruct Hx as [Hx|[Hx|Hx]]; [left; exact Hx | right; left; exact Hx |].
      right. right. right. exists c. split; [exact Hcin|]. right. right. exact Hx. }
    split; [exact (po_own _ _ _ _ HP0 x ltac:(clear - F4; lia) F1)|]. split; [apply Hvout; clear - Hx; lia|].
    exact (pri_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1). }
  assert (Hpc0 : ms_pc_val ms = wa 0x43e20) by (destruct Hd10 as (X & _); cbn [mrg s_pc L nq_front] in X; exact X).
  rewrite <- Hpc0 in A1.
  assert (Est : uE E (laddc (p_tg a) 2872) = TT + 2872).
  { rewrite uE_laddc_z by (rewrite Etg; fold TT; unfold two64; clear - B0; lia). rewrite Etg. reflexivity. }
  set (OWN_A := fun x : Z => (exists i, 1 <= i <= 31 /\ CA + 80 * i + 4 <= x < CA + 80 * i + 16) \/ RIv <= x < RIv + 8).
  assert (HAsp : 2064 <= uE E SPl <= 2^47) by (fold SP; clear - HSPr; lia).
  assert (HAst : uE E (laddc (p_tg a) 2872) + 16 <= 2^47) by (rewrite Est; clear - B0; lia).
  assert (HAown : forall x, 0 <= x < 2^64 -> OWN_A x -> own_pt E M x /\ outside E (s_rgs (mrg L Sp)) (wa x) /\ ~ frz_pt E M x).
  { intros x Hx HO1. apply Hvown. destruct HO1 as [(i & Hi & HO1)|HO1]; [left; clear - Hi HO1; lia | right; left; unfold RIv in HO1; clear - HO1 Hcr; lia]. }
  assert (HAfr : forall x, 0 <= x < 2^64 -> ~ (uE E SPl - 2064 <= x < uE E SPl) -> ~ (uE E (laddc (p_tg a) 2872) <= x < uE E (laddc (p_tg a) 2872) + 16) -> ~ OWN_A x ->
            mA (wa x) = mr (wa x)).
  { intros x Hx Hw _ HO1. fold SP in Hw. apply (A11 x Hx).
    - clear - Hw ESPq. lia.
    - intros i Hi Hc0. apply HO1. left. exists i. split; [exact Hi | exact Hc0].
    - intros Hc0. apply HO1. right. exact Hc0. }
  assert (HAgr : mem_grows mr mA) by (destruct A9 as (_ & _ & _ & _ & _ & _ & Hg); exact Hg).
  apply (den_run_app_x cfg LIMIT model0 Hwx mem0 L Sp E M ms model T SPl (laddc (p_tg a) 2872) 0%nat 2%nat cw cs 0x73c38 K34
           [3; 4]%nat R1 mA OWN_A 2064 ltac:(lia) Hd1 CwL eq_refl Pw Pst HAsp HAst k34_cases A1 A8 HAown HAfr HAgr).
  intros E1 ms1 model1 HD1 Ha1 Hfz1 Hrr1 Hvis1 HH1 Hrm1.
  set (Lh1 := hand_post L 0x73c38 K34 [0%nat; 2%nat]) in *.
  set (L1 := ecall_tpl L [0%nat; 2%nat] (l_rb a c)) in *.
  assert (HwfM : sm_wf (s_next L) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd1).
  pose proof (awf_pri _ a Haw) as Hwpri.
  assert (Hagr1 : forall E'', agree (s_next (mrg Lh1 Sp)) E1 E'' -> agree (s_next S) E E'').
  { intros E'' Ha''. apply (agree_trans _ E E1 E''); [exact Ha1 |
      apply (agree_mono _ (s_next (mrg Lh1 Sp))); [cbn [mrg Lh1 hand_post L nq_front s_next]; clear; lia | exact Ha'']]. }
  assert (Erb : uE E (l_rb a c) = RBv) by exact (u_lrb E a mem0 HI c Hcr).
  assert (Hwrb : lwf (s_next S) (l_rb a c) = true) by (unfold l_rb; apply lwf_laddc; exact (lwf_p_nth _ a 0 Hwpri)).
  assert (HDr1 : DEN ASEGS LIMIT model0 (ms_mem ms1) E1 (mrg L1 Sp) M ms1 model1).
  { change (mrg L1 Sp) with (with_regs_t (mrg Lh1 Sp) (s_regs L1)).
    apply den_regs_eq; [exact HD1|]. intros E'' Ha'' r.
    pose proof (dn_sden _ _ _ _ _ _ _ _ _ HD1 E'' Ha'') as (_ & _ & _ & Hregs & _).
    rewrite <- (Hregs r). cbn [restrict ms_regs]. rewrite Hrr1.
    unfold L1, ecall_tpl. fold Lh1. apply (with_regs_den E'' R1).
    - intros r'. pose proof (Hregs r') as X. cbn [restrict ms_regs mrg s_regs] in X. rewrite Hrr1 in X. symmetry. exact X.
    - destruct A2 as (Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q17).
      assert (Hlrb : lden E'' (l_rb a c) = wa RBv).
      { rewrite (lden_agree_wf (s_next S) E E'' (l_rb a c) Hwrb (Hagr1 E'' Ha'')).
        rewrite <- (Z_to_bv_bv_unsigned _ (lden E (l_rb a c))). fold (uE E (l_rb a c)). rewrite Erb. reflexivity. }
      repeat (constructor; [split; [intros Hc0; vm_compute in Hc0; discriminate | cbn [fst snd]; rewrite ?lden_lconst; first [rewrite Hlrb; symmetry; exact Q10 | symmetry; assumption]] |]).
      constructor. }
  (* [comment removed for export] *)
  assert (Ege : snd gP = GE) by exact (gkind_eqb_GE _ Cge).
  assert (Eu1 : uE E1 (l_rb a c) = RBv) by (rewrite (uE_agree (s_next S) E E1 _ Hwrb Ha1); exact Erb).
  assert (HbwS : bases_wf (s_next L) (s_rgs (mrg L Sp)) = true) by exact (dn_bases _ _ _ _ _ _ _ _ _ Hd1).
  assert (Hsh1 : shape (s_rgs (mrg L1 Sp)) = shape (s_rgs (mrg L Sp))).
  { cbn [mrg s_rgs]. unfold L1, ecall_tpl. rewrite with_regs_rgs. unfold hand_post. cbn [s_rgs]. unfold shape. rewrite !map_app. f_equal.
    pose proof (empty_at_shape [0%nat; 2%nat] (s_rgs L) 0) as Hs. unfold shape in Hs. exact Hs. }
  assert (Hout1 : forall x, outside E (s_rgs (mrg L Sp)) (wa x) -> outside E1 (s_rgs (mrg L1 Sp)) (wa x)).
  { intros x Hx. apply (outside_shape E1 (s_rgs (mrg L Sp))); [exact Hsh1|]. exact (proj1 (outside_agree (s_next L) E E1 _ _ HbwS Ha1) Hx). }
  assert (Hw64 : forall w, own_pt E M w -> 0 <= w < two64).
  { intros w Hw0. destruct (Z_lt_le_dec w two64) as [X|X].
    - destruct Hw0 as (q & Hq & Hqw). pose proof (uE_range E (fst q)) as Rq. clear - Hqw Rq X. lia.
    - exfalso. destruct (ha_ownx _ _ _ _ HA0 w (own_pt_a_M E M a w Hown_eq Hw0)) as [Dc|[_ Pf]].
      + destruct HA0 as [(n0 & F0 & st0 & I0 & _) _ _ _ _ _ _]. destruct I0 as [_ _ _ D1r _ _ _ _ _ B1r _ _ _].
        unfold dcov in Dc. unfold two64 in X. clear - Dc X D1r B1r. lia.
      + pose proof (pri_foot_rng E a mem0 HI w Pf) as Rpf. unfold two64 in X. clear - Rpf X. lia. }
  assert (HinPG : forall x, RBv <= x < RBv + 262144 \/ FAv <= x < FAv + 262144 -> z_pg pz <= x < z_pg pz + PG_SIZE).
  { intros x Hx. unfold RBv, FAv, PG_SIZE in *. clear - Hx B0 Hcr. lia. }
  assert (Hc1nr : forall fl, arg (mrg L1 Sp) 3 = Some fl -> mmap_noreserve_b (Z_to_bv 64 fl) = false).
  { intros fl Hfl. assert (Efl : fl = 50) by (vm_compute in Hfl; injection Hfl as <-; reflexivity). rewrite Efl. reflexivity. }
  assert (Hc1top : uE E1 (l_rb a c) + 262144 <= 2^47) by (rewrite Eu1; unfold RBv; clear - B0 Hcr; lia).
  assert (Hc1rg : forall R0, In R0 (s_rgs (mrg L1 Sp)) -> forall w, uE E1 (rg_base R0) <= w < uE E1 (rg_base R0) + rsz E1 R0 ->
            ~ (uE E1 (l_rb a c) <= w < uE E1 (l_rb a c) + 262144)).
  { intros R0 HR0 w Hw Hc0. rewrite Eu1 in Hc0.
    pose proof (Hout1 w (Hvout w ltac:(clear - Hc0; lia))) as Hou. unfold outside in Hou. rewrite Forall_forall in Hou. specialize (Hou R0 HR0).
    rewrite u_wa_small in Hou by (unfold RBv in Hc0; clear - Hc0 B0 Hcr; lia). unfold uE in Hw. clear - Hou Hw Hc0. lia. }
  assert (Hc1own : forall w, own_pt E1 M w -> ~ (uE E1 (l_rb a c) <= bv_unsigned (Z_to_bv 64 w) < uE E1 (l_rb a c) + 262144)).
  { intros w Hw Hc0. rewrite Eu1 in Hc0.
    assert (Hw0 : own_pt E M w) by exact (proj1 (own_pt_agree (s_next L) E E1 M w HwfM Ha1) Hw).
    rewrite u_small64 in Hc0 by exact (Hw64 w Hw0).
    destruct (virgin_not_own LIMIT model0 mem0 E S M ms model a Hd HA0 Hne Hown_eq c Hcin Z0 w Hw0) as [N1 _]. apply N1. exact Hc0. }
  assert (Hc1frz : forall w, frz_pt E1 M w -> ~ (uE E1 (l_rb a c) <= w < uE E1 (l_rb a c) + 262144)).
  { intros w Hw Hc0. rewrite Eu1 in Hc0.
    assert (Hw0 : frz_pt E M w) by exact (proj1 (frz_pt_agree (s_next L) E E1 M w HwfM Ha1) Hw).
    exact (pg_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne w (HinPG w ltac:(left; exact Hc0)) Hw0). }
  apply (den_commit_own cfg LIMIT model0 Hwx Hsegb Hoff Hrespos Hreswf (ms_mem ms1) (mrg L1 Sp) E1 M ms1 model1 T (l_rb a c) jP gP HDr1
           eq_refl eq_refl Cfk1 HgP Ege Hc1nr eq_refl Hc1top Hc1rg Hc1own Hc1frz).
  intros ms2 model2 Hms2 HDc1.
  (* [comment removed for export] *)
  set (Rro0 := RG (lconst 65536) (lconst zro) RO TEmpty) in *.
  set (VOWN := fun x : Z => CA - 128 <= x < CA + 2592 \/ SB + 137438953472 <= x < SB + 137438953472 + 4096 \/
                           SH + 536870912 * c <= x < SH + 536870912 * c + 32768 \/
                           SH + 536870912 * c + 469762048 <= x < SH + 536870912 * c + 469762048 + 32768).
  set (COV := fun x : Z => (exists R0, (R0 = Rro0 \/ In R0 rest) /\ uE E (rg_base R0) <= x < uE E (rg_base R0) + rsz E R0) \/
                           SP - 2064 <= x < SP \/ TT + 2872 <= x < TT + 2888 \/ VOWN x).
  assert (HwSP : lwf (s_next S) SPl = true).
  { pose proof CwL as X. unfold state_wf in X. apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. apply andb_prop in X as [X _].
    cbn [L nq_front s_regs s_next] in X. exact (regs_wf_n_get _ _ 31 X 2%nat ltac:(lia)). }
  assert (HwTG : lwf (s_next S) (p_tg a) = true) by exact (lwf_p_nth _ a 4 Hwpri).
  assert (Hcov_vis : forall Ei Li Mi msi modeli m0i c0 c2, DEN ASEGS LIMIT model0 m0i Ei (mrg Li Sp) Mi msi modeli -> agree (s_next S) E Ei ->
            nth_error (s_rgs Li) 0 = Some (RG (laddc SPl (-2064)) (lconst 2064) RW c0) -> nth_error (s_rgs Li) 1 = Some Rro0 ->
            nth_error (s_rgs Li) 2 = Some (RG (laddc (p_tg a) 2872) (lconst 16) RW c2) ->
            (forall p, In p (sm_own M) -> In p (sm_own Mi)) ->
            forall x, COV x -> Hof Ei Mi modeli (wa x) = false).
  { intros Ei Li Mi msi modeli m0i c0 c2 HDi Hai Q0 Q1 Q2 Hsub x Hc.
    assert (HinL : forall k R0, nth_error (s_rgs Li) k = Some R0 -> In R0 (s_rgs (mrg Li Sp))).
    { intros k0 R0 Hk0. cbn [mrg s_rgs]. apply in_or_app. left. exact (nth_error_In _ _ Hk0). }
    destruct Hc as [(R0 & HR0 & Hx)|[Hx|[Hx|Hx]]].
    - assert (HR0' : In R0 (s_rgs (mrg L Sp))).
      { cbn [mrg s_rgs L Sp nq_front nq_rest]. apply in_or_app. destruct HR0 as [->|HR0]; [left; exact (nth_error_In _ _ Pro) | right; exact HR0]. }
      unfold bases_wf in HbwS. rewrite forallb_forall in HbwS. destruct (andb_prop _ _ (HbwS R0 HR0')) as [Hb1 Hb2].
      apply (den_rg_vis LIMIT model0 m0i Ei (mrg Li Sp) Mi msi modeli R0 x HDi).
      + destruct HR0 as [->|HR0]; [exact (HinL 1%nat _ Q1) | cbn [mrg s_rgs Sp nq_rest]; apply in_or_app; right; exact HR0].
      + unfold uE, rsz in *. rewrite (lden_agree_wf _ E Ei _ Hb1 Hai), (lden_agree_wf _ E Ei _ Hb2 Hai). exact Hx.
    - apply (den_rg_vis LIMIT model0 m0i Ei (mrg Li Sp) Mi msi modeli _ x HDi (HinL 0%nat _ Q0)). cbn [rg_base]. unfold rsz. cbn [rg_size].
      rewrite lden_lconst, (u_small64 2064) by (unfold two64; lia). unfold uE. rewrite (lden_agree_wf _ E Ei _ (lwf_laddc _ _ _ HwSP) Hai).
      rewrite Ebw. clear - Hx. lia.
    - apply (den_rg_vis LIMIT model0 m0i Ei (mrg Li Sp) Mi msi modeli _ x HDi (HinL 2%nat _ Q2)). cbn [rg_base]. unfold rsz. cbn [rg_size].
      rewrite lden_lconst, (u_small64 16) by (unfold two64; lia). unfold uE. rewrite (lden_agree_wf _ E Ei _ (lwf_laddc _ _ _ HwTG) Hai).
      fold (uE E (laddc (p_tg a) 2872)). rewrite Est. clear - Hx. lia.
    - destruct (Hvown x Hx) as ((p & Hp & Hpw) & _).
      pose proof (sm_wf_own _ M HwfM) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw p Hp) as [Hf1 Hf2].
      cbn [L nq_front s_next] in Hf1, Hf2.
      refine (proj1 (dn_own _ _ _ _ _ _ _ _ _ HDi p (Hsub p Hp) x _)).
      unfold uE in *. rewrite (lden_agree_wf _ E Ei _ Hf1 Hai), (lden_agree_wf _ E Ei _ Hf2 Hai). exact Hpw. }
  (* [comment removed for export] *)
  assert (HENVrg : forall x, qENVC TP K TSDA PT x -> exists R0, (R0 = Rro0 \/ In R0 rest) /\ uE E (rg_base R0) <= x < uE E (rg_base R0) + rsz E R0).
  { intros x He. unfold qENVC in He.
    assert (Hnum : forall lo hi, In (lo, hi) ENVC_RNG -> lo <= x < hi -> exists R0, (R0 = Rro0 \/ In R0 rest) /\ uE E (rg_base R0) <= x < uE E (rg_base R0) + rsz E R0).
    { intros lo hi Hin Hx. unfold envc_ok in Cenv. rewrite forallb_forall in Cenv. specialize (Cenv (lo, hi) Hin). cbn [fst snd] in Cenv.
      unfold in_rg_const in Cenv. rewrite existsb_l_eq in Cenv. apply existsb_exists in Cenv as (R0 & HR0 & Hc0). cbn [Sp nq_rest s_rgs] in HR0.
      destruct (is_const (rg_base R0)) as [b0|] eqn:Eb0; [|discriminate]. destruct (is_const (rg_size R0)) as [z0|] eqn:Ez0; [|discriminate].
      destruct (Z.leb b0 lo) eqn:C1; [|discriminate]. apply Z.leb_le in C1, Hc0.
      exists R0. split; [right; exact HR0|]. unfold uE, rsz. rewrite (is_const_u E _ _ Eb0), (is_const_u E _ _ Ez0). clear - C1 Hc0 Hx. lia. }
    destruct He as [He|[He|[He|[He|[He|[He|[He|[He|[He|[He|[He|[He|He]]]]]]]]]]]].
    - exists Rro0. split; [left; reflexivity|]. unfold Rro0, uE, rsz. cbn [rg_base rg_size]. rewrite !lden_lconst, !u_small64 by (unfold two64; clear - Hzro; lia). clear - He Hzro. lia.
    - exact (Hnum 910448 910520 ltac:(cbn; auto 10) He).
    - exact (Hnum 918480 918488 ltac:(cbn; auto 10) He).
    - exact (Hnum 929848 929873 ltac:(cbn; auto 10) He).
    - exact (Hnum 941788 941800 ltac:(cbn; auto 10) He).
    - exact (Hnum 943736 943744 ltac:(cbn; auto 10) He).
    - exact (Hnum 947040 947064 ltac:(cbn; auto 10) He).
    - exact (Hnum 1532192 1532200 ltac:(cbn; auto 10) He).
    - exact (Hnum 1540664 1540672 ltac:(cbn; auto 10) He).
    - exact (Hnum 1540780 1540781 ltac:(cbn; auto 10) He).
    - destruct (rdw_in IMGP E mr rest _ 8 _ HRGrest ltac:(lia) WT1) as (R0 & HR0 & P1 & P2).
      rewrite uE_laddc_z, UTP in P1, P2 by (rewrite UTP; unfold two64; clear - CT5 CT6; lia).
      exists R0. split; [right; exact HR0|]. clear - P1 P2 He. cbn in P2. lia.
    - destruct (rdw_in IMGP E mr rest _ 8 _ HRGrest ltac:(lia) WT2) as (R0 & HR0 & P1 & P2).
      rewrite uE_laddc_z, UTS in P1, P2 by (rewrite UTS; unfold two64; clear - CT1 CT2 CT7 CT8; lia).
      exists R0. split; [right; exact HR0|]. clear - P1 P2 He. cbn in P2. lia.
    - exists Rpt. split; [right; exact HRpt|]. rewrite EPT152 in Ppt1, Ppt2. clear - Ppt1 Ppt2 He. cbn in Ppt2. lia. }
  (* [comment removed for export] *)
  pose proof (FW _ (nth_error_In FU_WORDS 0 eq_refl)) as FW0. pose proof (FW _ (nth_error_In FU_WORDS 1 eq_refl)) as FW1.
  pose proof (FW _ (nth_error_In FU_WORDS 2 eq_refl)) as FW2. pose proof (FW _ (nth_error_In FU_WORDS 3 eq_refl)) as FW3.
  pose proof (FW _ (nth_error_In FU_WORDS 4 eq_refl)) as FW4. pose proof (FW _ (nth_error_In FU_WORDS 5 eq_refl)) as FW5.
  pose proof (FW _ (nth_error_In FU_WORDS 6 eq_refl)) as FW6. pose proof (FW _ (nth_error_In FU_WORDS 7 eq_refl)) as FW7.
  pose proof (FW _ (nth_error_In FU_WORDS 8 eq_refl)) as FW8. pose proof (FW _ (nth_error_In FU_WORDS 9 eq_refl)) as FW9.
  pose proof (FW _ (nth_error_In FU_WORDS 10 eq_refl)) as FW10. pose proof (FW _ (nth_error_In FU_WORDS 11 eq_refl)) as FW11.
  pose proof (FW _ (nth_error_In FU_WORDS 12 eq_refl)) as FW12. pose proof (FW _ (nth_error_In FU_WORDS 13 eq_refl)) as FW13.
  pose proof (FW _ (nth_error_In FU_WORDS 14 eq_refl)) as FW14. pose proof (FW _ (nth_error_In FU_WORDS 15 eq_refl)) as FW15.
  pose proof (FW _ (nth_error_In FU_WORDS 16 eq_refl)) as FW16. pose proof (FW _ (nth_error_In FU_WORDS 17 eq_refl)) as FW17.
  pose proof (FW _ (nth_error_In FU_WORDS 18 eq_refl)) as FW18.
  cbn [fst snd] in FW0, FW1, FW2, FW3, FW4, FW5, FW6, FW7, FW8, FW9, FW10, FW11, FW12, FW13, FW14, FW15, FW16, FW17, FW18.
  (* [comment removed for export] *)
  set (M2 := with_own M (sm_own M ++ [(l_rb a c, lconst 262144)])) in *.
  set (L1p := fix_post L1 (l_rb a c)) in *.
  change (fix_post (mrg L1 Sp) (l_rb a c)) with (mrg L1p Sp) in HDc1.
  rewrite Eu1 in HDc1.
  set (H2 := Hof E1 M2 model2) in *. set (msr2 := restrict H2 ms2) in *.
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ HDr1)) as Hdr10.
  assert (Hpc1 : ms_pc_val ms1 = Z_to_bv 64 0x73c38) by (destruct Hdr10 as (X & _); exact X).
  assert (Ead : lden E1 (l_rb a c) = wa RBv).
  { rewrite <- (Z_to_bv_bv_unsigned _ (lden E1 (l_rb a c))). fold (uE E1 (l_rb a c)). rewrite Eu1. reflexivity. }
  pose proof (fresh_restrict H2 ms1 false (lden E1 (l_rb a c)) (Z_to_bv 64 262144) 0x73c38 Hpc1) as FR2.
  rewrite <- Hms2 in FR2. fold msr2 in FR2. rewrite Ead, Hrr1 in FR2.
  set (mB0' := ms_mem msr2) in *.
  assert (EmB0 : mB0' = mrestrict H2 (fresh_mem false (ms_mem ms1) (wa RBv) (Z_to_bv 64 262144))) by (unfold mB0'; rewrite FR2; reflexivity).
  assert (Ereg2 : ms_regs ms2 = rupd R1 a0r (wa RBv)) by (change (ms_regs ms2) with (ms_regs msr2); rewrite FR2; reflexivity).
  assert (Epc2 : ms_pc_val ms2 = wa 0x73c3c) by (change (ms_pc_val ms2) with (ms_pc_val msr2); rewrite FR2; reflexivity).
  (* [comment removed for export] *)
  assert (Hlf3 : length front = 3%nat).
  { assert (A1' : (length front <= 3)%nat) by (unfold front; rewrite length_firstn; apply Nat.le_min_l).
    assert (A2' : (2 < length front)%nat) by (apply nth_error_Some; rewrite Pst; discriminate). clear - A1' A2'. lia. }
  pose proof (list3_eq front _ _ _ Hlf3 Pw Pro Pst) as Efront.
  set (FRl := [RG (laddc SPl (-2064)) (lconst 2064) RW TEmpty; Rro0; RG (laddc (p_tg a) 2872) (lconst 16) RW TEmpty]).
  assert (EfrH : forall q0 K0, s_rgs (hand_post L q0 K0 [0%nat; 2%nat]) = FRl).
  { intros q0 K0. unfold hand_post. cbn [s_rgs L nq_front]. rewrite Efront. reflexivity. }
  assert (Efr1 : s_rgs L1p = FRl) by (unfold L1p, fix_post; cbn [s_rgs]; unfold L1, ecall_tpl; rewrite with_regs_rgs; apply EfrH).
  assert (Hsub2 : forall p, In p (sm_own M) -> In p (sm_own M2)) by (intros p Hp; cbn [M2 with_own sm_own]; apply in_or_app; left; exact Hp).
  assert (Hcov0 : forall x, COV x -> Hof E M model (wa x) = false).
  { intros x Hc. exact (Hcov_vis E L M ms model mem0 cw cs Hd1 (agree_refl _ _) Pw Pro Pst (fun p Hp => Hp) x Hc). }
  assert (Hcov2 : forall x, COV x -> H2 (wa x) = false).
  { intros x Hc. refine (Hcov_vis E1 L1p M2 ms2 model2 _ TEmpty TEmpty HDc1 Ha1 _ _ _ Hsub2 x Hc); rewrite Efr1; reflexivity. }
  assert (HmB0 : forall x, 0 <= x < 2^64 -> COV x -> ~ (RBv <= x < RBv + 262144) -> mB0' (wa x) = mA (wa x)).
  { intros x Hx Hc Hnr. rewrite EmB0. unfold mrestrict. rewrite (Hcov2 x Hc).
    rewrite fresh_mem_out; [exact (Hvis1 _ (Hcov0 x Hc))|].
    change (Z_to_bv 64 262144) with (wa 262144). rewrite !u_wa_small by (first [exact Hx | unfold RBv; clear - B0 Hcr; lia | clear; lia]). exact Hnr. }
  (* [comment removed for export] *)
  assert (HcB : forall x, qCELLS_B CA c SB SPq TP K TSDA PT TT x -> COV x /\ ~ (RBv <= x < RBv + 262144) /\ ~ (FAv <= x < FAv + 262144)).
  { intros x Hx. unfold qCELLS_B in Hx. cbv zeta in Hx. fold SHv SHFv in Hx. rewrite ESHv, ESHFv in Hx.
    destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]]].
    - split; [right; left; clear - Hx ESPq; lia|]. unfold RBv, FAv. clear - Hx B0 BP Hcr HSPr ESPq. lia.
    - split; [right; right; right; left; clear - Hx; lia|]. unfold RBv, FAv. clear - Hx T1 B0 Hcr. lia.
    - split; [right; right; right; right; left; clear - Hx Hcr; lia|]. unfold RBv, FAv. clear - Hx B0 Hcr. lia.
    - split; [right; right; left; exact Hx|]. unfold RBv, FAv. clear - Hx Hdisj B0 Hcr. unfold PG_SIZE in Hdisj. fold TT in Hdisj. lia.
    - split; [right; right; right; right; right; left; exact Hx|]. unfold RBv, FAv. clear - Hx S1 B0 Hcr. lia.
    - split; [right; right; right; right; right; right; exact Hx|]. unfold RBv, FAv. clear - Hx S1 B0 Hcr. lia.
    - split; [left; exact (HENVrg x Hx)|]. pose proof (HENV x Hx) as Hn. unfold qCHC in Hn. cbv zeta in Hn. unfold RBv, FAv. clear - Hn. lia. }
  assert (HB0 : agree_on (qCELLS_B CA c SB SPq TP K TSDA PT TT) mB0' (qmB0 mA c SB)).
  { intros x Hx Hcl. destruct (HcB x Hcl) as (Hc & Hn1 & _). unfold qmB0. rewrite kz_out by (first [exact Hx | exact Hn1]). exact (HmB0 x Hx Hc Hn1). }
  (* [comment removed for export] *)
  destruct A2 as (A2_10 & A2_11 & A2_12 & A2_13 & A2_14 & A2_15 & A2_17).
  assert (QB1 : getr (ms_regs ms2) (1%bv : reg) = wa 481784).
  { replace (1%bv : reg) with (Z_to_bv 5 1) by (apply bv_eq; reflexivity). rewrite Ereg2, getr_rupd_other by regne. exact A3. }
  assert (QB2 : getr (ms_regs ms2) (2%bv : reg) = wa (SPq - 400)).
  { replace (2%bv : reg) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity). rewrite Ereg2, getr_rupd_other by regne. exact A4. }
  assert (QB4 : getr (ms_regs ms2) (4%bv : reg) = wa TP).
  { replace (4%bv : reg) with (Z_to_bv 5 4) by (apply bv_eq; reflexivity). rewrite Ereg2, getr_rupd_other by regne.
    rewrite <- R4. exact (A8 4%nat ltac:(right; left; reflexivity)). }
  assert (QB8 : getr (ms_regs ms2) (8%bv : reg) = wa 262144).
  { replace (8%bv : reg) with (Z_to_bv 5 8) by (apply bv_eq; reflexivity). rewrite Ereg2, getr_rupd_other by regne. exact A5. }
  assert (QB10 : getr (ms_regs ms2) (10%bv : reg) = wa RBv).
  { replace (10%bv : reg) with a0r by (apply bv_eq; reflexivity). rewrite Ereg2. apply getr_rupd_same. regne. }
  assert (QB21 : getr (ms_regs ms2) (21%bv : reg) = wa (sz_tbl c)).
  { replace (21%bv : reg) with (Z_to_bv 5 21) by (apply bv_eq; reflexivity). rewrite Ereg2, getr_rupd_other by regne. exact A6. }
  assert (QB22 : getr (ms_regs ms2) (22%bv : reg) = wa 929816).
  { replace (22%bv : reg) with (Z_to_bv 5 22) by (apply bv_eq; reflexivity). rewrite Ereg2, getr_rupd_other by regne. exact A7. }
  assert (HCT : CA = TT + 208) by (clear - B0; lia).
  assert (HK : 0 <= K <= 1023) by (clear - CT1 CT2; lia).
  assert (Hvals : 0 <= st < 2^64 /\ 0 <= st2 < 2^64 /\ 0 <= mm1 < 2^64 /\ 0 <= mm2 < 2^64) by (clear - Hst Hst2 Hmm1 Hmm2; lia).
  assert (Iwsh' : wr mr SHv 32768) by (rewrite ESHv; exact Iwsh).
  assert (Iwshf' : wr mr SHFv 32768) by (rewrite ESHFv; exact Iwshf).
  destruct (@qstageB (mkFP (ms_fregs ms2) (ms_fcsr ms2)) (ms_rom ms2) mr mA regs (CA - 128) CA c SB SPq st st2 TP K TSDA PT TT mm1 mm2 sz mp
              Hc24 HSPp HSP16 HSTK eq_refl HSEPQ HCA' HCT HSB' HSEP' HO HK Hvals HENV HSHs Ist2 Iwc Iri Iwri Imm1 Imm2 Iwt Iwsh'
              FW6 FW0 FW1 FW2 FW3 FW4 FW7 FW8 FW9 FW10 FW11 FW12 FW13 FW14 FW15 FW16 FW17 FW18 Itls2 Itls3 Itls4 Itls5 A9
              mB0' HB0 (ms_regs ms2) QB1 QB2 QB4 QB8 QB10 QB21 QB22)
    as (RB2 & mB & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & HPB & HFB).
  (* [comment removed for export] *)
  assert (Hn33 : (s_next S <= s_next (hand_post L 0x73c38 K34 [0%nat; 2%nat]))%positive) by (cbn [hand_post L nq_front s_next]; clear; lia).
  assert (HwL1p : state_wf L1p = true).
  { unfold L1p. apply fix_post_wf.
    - unfold L1, ecall_tpl. apply with_regs_wf; [exact (hand_post_wf L _ _ _ CwL)|].
      repeat (constructor; [split; [intros Hc0; vm_compute in Hc0; discriminate | cbn [fst snd]; first [exact (lwf_mono' _ _ _ Hn33 Hwrb) | apply lwf_lconst]] |]). constructor.
    - unfold L1, ecall_tpl. rewrite with_regs_next. exact (lwf_mono' _ _ _ Hn33 Hwrb). }
  assert (Pw2 : nth_error (s_rgs L1p) 0 = Some (RG (laddc SPl (-2064)) (lconst 2064) RW TEmpty)) by (rewrite Efr1; reflexivity).
  assert (Pst2 : nth_error (s_rgs L1p) 2 = Some (RG (laddc (p_tg a) 2872) (lconst 16) RW TEmpty)) by (rewrite Efr1; reflexivity).
  assert (Esp1 : uE E1 SPl = SP) by exact (uE_agree (s_next S) E E1 _ HwSP Ha1).
  assert (Est1 : uE E1 (laddc (p_tg a) 2872) = TT + 2872) by (rewrite (uE_agree (s_next S) E E1 _ (lwf_laddc _ _ _ HwTG) Ha1); exact Est).
  set (OWN_B := fun x : Z => SHv <= x < SHv + 32768 \/ RIv + 48 <= x < RIv + 56 \/ CA + 2584 <= x < CA + 2592).
  assert (HBsp : 2064 <= uE E1 SPl <= 2^47) by (rewrite Esp1; clear - HSPr; lia).
  assert (HBst : uE E1 (laddc (p_tg a) 2872) + 16 <= 2^47) by (rewrite Est1; clear - B0; lia).
  assert (HBkeep : forall k, In k [3; 4]%nat -> getr RB2 (Z_to_bv 5 (Z.of_nat k)) = getr (ms_regs ms2) (Z_to_bv 5 (Z.of_nat k))).
  { intros k [<-|[<-|[]]]; [exact B9|]. rewrite B8. symmetry. replace (Z_to_bv 5 (Z.of_nat 4)) with (4%bv : reg) by (apply bv_eq; reflexivity). exact QB4. }
  assert (HBown : forall x, 0 <= x < 2^64 -> OWN_B x -> own_pt E1 M2 x /\ outside E1 (s_rgs (mrg L1p Sp)) (wa x) /\ ~ frz_pt E1 M2 x).
  { intros x Hx HO1. assert (Hv : VOWN x).
    { unfold VOWN. unfold OWN_B in HO1. rewrite ESHv in HO1. unfold RIv in HO1.
      destruct HO1 as [HO1|[HO1|HO1]]; [right; right; left; exact HO1 | right; left; clear - HO1 Hcr; lia | left; clear - HO1; lia]. }
    destruct (Hvown x Hv) as (V1 & V2 & V3). split; [|split].
    - destruct (proj2 (own_pt_agree (s_next L) E E1 M x HwfM Ha1) V1) as (p & Hp & Hpw). exists p. split; [exact (Hsub2 p Hp) | exact Hpw].
    - exact (Hout1 x V2).
    - intros Hf. apply V3. exact (proj1 (frz_pt_agree (s_next L) E E1 M x HwfM Ha1) Hf). }
  assert (HBfr : forall x, 0 <= x < 2^64 -> ~ (uE E1 SPl - 2064 <= x < uE E1 SPl) ->
            ~ (uE E1 (laddc (p_tg a) 2872) <= x < uE E1 (laddc (p_tg a) 2872) + 16) -> ~ OWN_B x -> mB (wa x) = mB0' (wa x)).
  { intros x Hx Hw Hs HO1. rewrite Esp1 in Hw. rewrite Est1 in Hs. destruct HFB as [HFB1 _]. apply (HFB1 x Hx).
    - clear - Hw ESPq. lia.
    - intros Hc0. apply HO1. left. exact Hc0.
    - intros Hc0. apply HO1. right. left. exact Hc0.
    - intros Hc0. apply HO1. right. right. exact Hc0.
    - clear - Hs. lia. }
  rewrite <- Epc2 in B1.
  apply (den_run_app_x cfg LIMIT model0 Hwx _ L1p Sp E1 M2 ms2 model2 T SPl (laddc (p_tg a) 2872) 0%nat 2%nat TEmpty TEmpty 0x73c38 K34
           [3; 4]%nat RB2 mB OWN_B 2064 ltac:(lia) HDc1 HwL1p eq_refl Pw2 Pst2 HBsp HBst k34_cases B1 HBkeep HBown HBfr (proj2 HFB)).
  intros E2 ms3 model3 HD3 Ha3 Hfz3 Hrr3 Hvis3 HH3 Hrm3.
  (* [comment removed for export] *)
  set (Lh2 := hand_post L1p 0x73c38 K34 [0%nat; 2%nat]) in *.
  set (L2 := ecall_tpl L1p [0%nat; 2%nat] (l_fa a c)) in *.
  assert (HwfM2 : sm_wf (s_next L1p) M2 = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ HDc1).
  assert (Hn1p : (s_next S <= s_next L1p)%positive) by (unfold L1p, fix_post; cbn [s_next]; unfold L1, ecall_tpl; rewrite with_regs_next; exact Hn33).
  assert (Ha13 : agree (s_next S) E E2).
  { apply (agree_trans _ E E1 E2); [exact Ha1|]. exact (agree_mono _ (s_next L1p) _ _ Hn1p Ha3). }
  assert (Hagr2 : forall E'', agree (s_next (mrg Lh2 Sp)) E2 E'' -> agree (s_next S) E E'').
  { intros E'' Ha''. apply (agree_trans _ E E2 E''); [exact Ha13|].
    apply (agree_mono _ (s_next (mrg Lh2 Sp))); [cbn [mrg Lh2 hand_post s_next]; clear - Hn1p; lia | exact Ha'']. }
  assert (Efa : uE E (l_fa a c) = FAv).
  { unfold l_fa. rewrite uE_laddc_z by (rewrite Esb; fold SB; unfold two64; clear - B0 Hcr; lia). rewrite Esb. unfold FAv. fold SB. ring. }
  assert (Hwfa : lwf (s_next S) (l_fa a c) = true) by (unfold l_fa; apply lwf_laddc; exact (lwf_p_nth _ a 0 Hwpri)).
  assert (HDr2 : DEN ASEGS LIMIT model0 (ms_mem ms3) E2 (mrg L2 Sp) M2 ms3 model3).
  { change (mrg L2 Sp) with (with_regs_t (mrg Lh2 Sp) (s_regs L2)).
    apply den_regs_eq; [exact HD3|]. intros E'' Ha'' r.
    pose proof (dn_sden _ _ _ _ _ _ _ _ _ HD3 E'' Ha'') as (_ & _ & _ & Hregs & _).
    rewrite <- (Hregs r). cbn [restrict ms_regs]. rewrite Hrr3.
    unfold L2, ecall_tpl. fold Lh2. apply (with_regs_den E'' RB2).
    - intros r'. pose proof (Hregs r') as X. cbn [restrict ms_regs mrg s_regs] in X. rewrite Hrr3 in X. symmetry. exact X.
    - destruct B2 as (Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q17).
      assert (Hlfa : lden E'' (l_fa a c) = wa FAv).
      { rewrite (lden_agree_wf (s_next S) E E'' (l_fa a c) Hwfa (Hagr2 E'' Ha'')).
        rewrite <- (Z_to_bv_bv_unsigned _ (lden E (l_fa a c))). fold (uE E (l_fa a c)). rewrite Efa. reflexivity. }
      repeat (constructor; [split; [intros Hc0; vm_compute in Hc0; discriminate | cbn [fst snd]; rewrite ?lden_lconst; first [rewrite Hlfa; symmetry; exact Q10 | symmetry; assumption]] |]).
      constructor. }
  (* [comment removed for export] *)
  assert (Eu2 : uE E2 (l_fa a c) = FAv) by (rewrite (uE_agree (s_next S) E E2 _ Hwfa Ha13); exact Efa).
  assert (Efr2 : s_rgs L2 = FRl) by (unfold L2, ecall_tpl; rewrite with_regs_rgs; unfold hand_post; cbn [s_rgs]; rewrite Efr1; reflexivity).
  assert (Hsh2 : shape (s_rgs (mrg L2 Sp)) = shape (s_rgs (mrg L Sp))).
  { cbn [mrg s_rgs]. rewrite Efr2. cbn [L nq_front s_rgs]. rewrite Efront. reflexivity. }
  assert (Hout2 : forall x, outside E (s_rgs (mrg L Sp)) (wa x) -> outside E2 (s_rgs (mrg L2 Sp)) (wa x)).
  { intros x Hx. apply (outside_shape E2 (s_rgs (mrg L Sp))); [exact Hsh2|]. exact (proj1 (outside_agree (s_next L) E E2 _ _ HbwS Ha13) Hx). }
  assert (Hc2nr : forall fl, arg (mrg L2 Sp) 3 = Some fl -> mmap_noreserve_b (Z_to_bv 64 fl) = false).
  { intros fl Hfl. assert (Efl : fl = 50) by (vm_compute in Hfl; injection Hfl as <-; reflexivity). rewrite Efl. reflexivity. }
  assert (Hc2top : uE E2 (l_fa a c) + 262144 <= 2^47) by (rewrite Eu2; unfold FAv; clear - B0 Hcr; lia).
  assert (Hc2rg : forall R0, In R0 (s_rgs (mrg L2 Sp)) -> forall w, uE E2 (rg_base R0) <= w < uE E2 (rg_base R0) + rsz E2 R0 ->
            ~ (uE E2 (l_fa a c) <= w < uE E2 (l_fa a c) + 262144)).
  { intros R0 HR0 w Hw Hc0. rewrite Eu2 in Hc0.
    pose proof (Hout2 w (Hvout w ltac:(clear - Hc0; lia))) as Hou. unfold outside in Hou. rewrite Forall_forall in Hou. specialize (Hou R0 HR0).
    rewrite u_wa_small in Hou by (unfold FAv in Hc0; clear - Hc0 B0 Hcr; lia). unfold uE in Hw. clear - Hou Hw Hc0. lia. }
  assert (Hc2own : forall w, own_pt E2 M2 w -> ~ (uE E2 (l_fa a c) <= bv_unsigned (Z_to_bv 64 w) < uE E2 (l_fa a c) + 262144)).
  { intros w Hw Hc0. rewrite Eu2 in Hc0.
    destruct (proj1 (own_pt_agree (s_next L1p) E1 E2 M2 w HwfM2 Ha3) Hw) as (p & Hp & Hpw).
    cbn [M2 with_own sm_own] in Hp. apply in_app_or in Hp as [Hp|[<-|[]]].
    - assert (Hw0 : own_pt E M w) by exact (proj1 (own_pt_agree (s_next L) E E1 M w HwfM Ha1) (ex_intro _ p (conj Hp Hpw))).
      rewrite u_small64 in Hc0 by exact (Hw64 w Hw0).
      destruct (virgin_not_own LIMIT model0 mem0 E S M ms model a Hd HA0 Hne Hown_eq c Hcin Z0 w Hw0) as [_ N2]. apply N2. exact Hc0.
    - cbn [fst snd] in Hpw. rewrite Eu1, uE_lc in Hpw by (clear; lia).
      rewrite u_small64 in Hc0 by (unfold RBv, two64 in *; clear - Hpw B0 Hcr; lia). unfold RBv, FAv in *. clear - Hpw Hc0. lia. }
  assert (Hc2frz : forall w, frz_pt E2 M2 w -> ~ (uE E2 (l_fa a c) <= w < uE E2 (l_fa a c) + 262144)).
  { intros w Hw Hc0. rewrite Eu2 in Hc0.
    assert (Hw1 : frz_pt E1 M w) by exact (proj1 (frz_pt_agree (s_next L1p) E1 E2 M2 w HwfM2 Ha3) Hw).
    assert (Hw0 : frz_pt E M w) by exact (proj1 (frz_pt_agree (s_next L) E E1 M w HwfM Ha1) Hw1).
    exact (pg_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne w (HinPG w ltac:(right; exact Hc0)) Hw0). }
  apply (den_commit_own cfg LIMIT model0 Hwx Hsegb Hoff Hrespos Hreswf (ms_mem ms3) (mrg L2 Sp) E2 M2 ms3 model3 T (l_fa a c) jP gP HDr2
           eq_refl eq_refl Cfk2 HgP Ege Hc2nr eq_refl Hc2top Hc2rg Hc2own Hc2frz).
  intros ms4 model4 Hms4 HDc2.
  (* [comment removed for export] *)
  set (M4 := with_own M2 (sm_own M2 ++ [(l_fa a c, lconst 262144)])) in *.
  set (L2p := fix_post L2 (l_fa a c)) in *.
  change (fix_post (mrg L2 Sp) (l_fa a c)) with (mrg L2p Sp) in HDc2.
  rewrite Eu2 in HDc2.
  set (H4 := Hof E2 M4 model4) in *. set (msr4 := restrict H4 ms4) in *.
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ HDr2)) as Hdr20.
  assert (Hpc3 : ms_pc_val ms3 = Z_to_bv 64 0x73c38) by (destruct Hdr20 as (X & _); exact X).
  assert (Ead2 : lden E2 (l_fa a c) = wa FAv).
  { rewrite <- (Z_to_bv_bv_unsigned _ (lden E2 (l_fa a c))). fold (uE E2 (l_fa a c)). rewrite Eu2. reflexivity. }
  pose proof (fresh_restrict H4 ms3 false (lden E2 (l_fa a c)) (Z_to_bv 64 262144) 0x73c38 Hpc3) as FR4.
  rewrite <- Hms4 in FR4. fold msr4 in FR4. rewrite Ead2, Hrr3 in FR4.
  set (mC0' := ms_mem msr4) in *.
  assert (EmC0 : mC0' = mrestrict H4 (fresh_mem false (ms_mem ms3) (wa FAv) (Z_to_bv 64 262144))) by (unfold mC0'; rewrite FR4; reflexivity).
  assert (Ereg4 : ms_regs ms4 = rupd RB2 a0r (wa FAv)) by (change (ms_regs ms4) with (ms_regs msr4); rewrite FR4; reflexivity).
  assert (Epc4 : ms_pc_val ms4 = wa 0x73c3c) by (change (ms_pc_val ms4) with (ms_pc_val msr4); rewrite FR4; reflexivity).
  assert (Efr2p : s_rgs L2p = FRl) by (unfold L2p, fix_post; cbn [s_rgs]; exact Efr2).
  assert (Hsub4 : forall p, In p (sm_own M) -> In p (sm_own M4)).
  { intros p Hp. cbn [M4 with_own sm_own]. apply in_or_app. left. exact (Hsub2 p Hp). }
  assert (Hcov4 : forall x, COV x -> H4 (wa x) = false).
  { intros x Hc. refine (Hcov_vis E2 L2p M4 ms4 model4 _ TEmpty TEmpty HDc2 Ha13 _ _ _ Hsub4 x Hc); rewrite Efr2p; reflexivity. }
  assert (HmC0 : forall x, 0 <= x < 2^64 -> COV x -> ~ (FAv <= x < FAv + 262144) -> mC0' (wa x) = mB (wa x)).
  { intros x Hx Hc Hnr. rewrite EmC0. unfold mrestrict. rewrite (Hcov4 x Hc).
    rewrite fresh_mem_out; [exact (Hvis3 _ (Hcov2 x Hc))|].
    change (Z_to_bv 64 262144) with (wa 262144). rewrite !u_wa_small by (first [exact Hx | unfold FAv; clear - B0 Hcr; lia | clear; lia]). exact Hnr. }
  assert (HmC0fa : forall x, FAv <= x < FAv + 262144 -> mC0' (wa x) = Some (Z_to_bv 8 0)).
  { intros x Hx. rewrite EmC0. unfold mrestrict.
    assert (Hv4 : H4 (wa x) = false).
    { refine (proj1 (dn_own _ _ _ _ _ _ _ _ _ HDc2 (l_fa a c, lconst 262144) _ x _)).
      - cbn [M4 with_own sm_own]. apply in_or_app. right. left. reflexivity.
      - cbn [fst snd]. rewrite Eu2, uE_lc by (clear; lia). exact Hx. }
    rewrite Hv4. apply fresh_mem_in. change (Z_to_bv 64 262144) with (wa 262144).
    rewrite !u_wa_small by (first [unfold FAv in *; clear - Hx B0 Hcr; lia | clear; lia]). exact Hx. }
  assert (HC0 : agree_on (qCELLS_C CA c SB SPq TP K TSDA PT TT) mC0' (kz mB FAv 262144)).
  { intros x Hx [Hcl|Hfa].
    - destruct (HcB x Hcl) as (Hc & _ & Hn2). rewrite kz_out by (first [exact Hx | exact Hn2]). exact (HmC0 x Hx Hc Hn2).
    - rewrite kz_in by (first [exact Hx | exact Hfa]). exact (HmC0fa x Hfa). }
  destruct B2 as (B2_10 & B2_11 & B2_12 & B2_13 & B2_14 & B2_15 & B2_17).
  assert (QC1 : getr (ms_regs ms4) (1%bv : reg) = wa 481784).
  { replace (1%bv : reg) with (Z_to_bv 5 1) by (apply bv_eq; reflexivity). rewrite Ereg4, getr_rupd_other by regne. exact B3. }
  assert (QC2 : getr (ms_regs ms4) (2%bv : reg) = wa (SPq - 448)).
  { replace (2%bv : reg) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity). rewrite Ereg4, getr_rupd_other by regne. exact B4. }
  assert (QC4 : getr (ms_regs ms4) (4%bv : reg) = wa TP).
  { replace (4%bv : reg) with (Z_to_bv 5 4) by (apply bv_eq; reflexivity). rewrite Ereg4, getr_rupd_other by regne. exact B8. }
  assert (QC8 : getr (ms_regs ms4) (8%bv : reg) = wa 262144).
  { replace (8%bv : reg) with (Z_to_bv 5 8) by (apply bv_eq; reflexivity). rewrite Ereg4, getr_rupd_other by regne. exact B5. }
  assert (QC10 : getr (ms_regs ms4) (10%bv : reg) = wa FAv).
  { replace (10%bv : reg) with a0r by (apply bv_eq; reflexivity). rewrite Ereg4. apply getr_rupd_same. regne. }
  assert (QC21 : getr (ms_regs ms4) (21%bv : reg) = wa (sz_tbl c)).
  { replace (21%bv : reg) with (Z_to_bv 5 21) by (apply bv_eq; reflexivity). rewrite Ereg4, getr_rupd_other by regne. exact B6. }
  assert (QC22 : getr (ms_regs ms4) (22%bv : reg) = wa 929816).
  { replace (22%bv : reg) with (Z_to_bv 5 22) by (apply bv_eq; reflexivity). rewrite Ereg4, getr_rupd_other by regne. exact B7. }
  (* [comment removed for export] *)
  assert (HvisRB0 : forall x, RBv <= x < RBv + 262144 -> H2 (wa x) = false /\ H4 (wa x) = false).
  { intros x Hx. split.
    - refine (proj1 (dn_own _ _ _ _ _ _ _ _ _ HDc1 (l_rb a c, lconst 262144) _ x _)); [cbn [M2 with_own sm_own]; apply in_or_app; right; left; reflexivity|].
      cbn [fst snd]. rewrite Eu1, uE_lc by (clear; lia). exact Hx.
    - refine (proj1 (dn_own _ _ _ _ _ _ _ _ _ HDc2 (l_rb a c, lconst 262144) _ x _)); [cbn [M4 M2 with_own sm_own]; apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
      cbn [fst snd]. rewrite (uE_agree (s_next S) E E2 _ Hwrb Ha13), Erb, uE_lc by (clear; lia). exact Hx. }
  pose proof HFB as HFBc. destruct HFBc as [HFB1c _]. fold SHv in HFB1c. rewrite ESHv in HFB1c. fold RIv in HFB1c.
  assert (HzeroC : forall x, RBv <= x < RBv + 262144 -> mC0' (wa x) = Some (Z_to_bv 8 0)).
  { intros x Hx. destruct (HvisRB0 x Hx) as [V2 V4]. assert (Hx64 : 0 <= x < 2^64) by (unfold RBv in Hx; clear - Hx B0 Hcr; lia).
    rewrite EmC0. unfold mrestrict. rewrite V4. rewrite fresh_mem_out.
    2:{ change (Z_to_bv 64 262144) with (wa 262144). rewrite !u_wa_small by (first [exact Hx64 | unfold FAv; clear - B0 Hcr; lia | clear; lia]). unfold RBv, FAv in *. clear - Hx. lia. }
    rewrite (Hvis3 _ V2). rewrite (HFB1c x Hx64).
    2:{ unfold RBv in Hx. clear - Hx B0 BP Hcr HSPr ESPq. lia. }
    2:{ unfold RBv in Hx. clear - Hx S1 B0 Hcr. lia. }
    2:{ unfold RIv, RBv in *. clear - Hx B0 Hcr. lia. }
    2:{ unfold RBv in Hx. clear - Hx T1 B0 Hcr. lia. }
    2:{ unfold RBv in Hx. clear - Hx Hdisj B0 Hcr. unfold PG_SIZE in Hdisj. fold TT in Hdisj. lia. }
    rewrite EmB0. unfold mrestrict. rewrite V2. apply fresh_mem_in.
    change (Z_to_bv 64 262144) with (wa 262144). rewrite !u_wa_small by (first [exact Hx64 | unfold RBv; clear - B0 Hcr; lia | clear; lia]). exact Hx. }
  assert (HWB : wr mC0' RBv 8192).
  { apply wr_bytes; [unfold RBv; clear - B0 Hcr; lia | unfold RBv; clear - B0 Hcr; lia|]. intros x Hx.
    unfold wview. rewrite (HzeroC x ltac:(clear - Hx; lia)). discriminate. }
  destruct (@qstageC (mkFP (ms_fregs ms4) (ms_fcsr ms4)) (ms_rom ms4) mr mA regs (CA - 128) CA c SB SPq st st2 TP K TSDA PT TT mm1 mm2 sz mp mx
              Hc24 HSPp HSP16 HSTK R1b R9b R22b eq_refl HSEPQ Hfm Rq0 Rqb Hwq HCA' HCT HSB' HSEP' HO HK Hvals HENV HSHs HSHF Ist Iwc Iri Iwri Iwt Iwshf' RSB RRIB
              FW2 FW3 FW7 FW8 FW9 FW10 FW11 FW12 FW13 FW14 FW15 FW16 FW17 FW18 Itls2 Itls3 Itls4 Itls5 HIMG A9
              mB0' HB0 mB mC0' HPB HFB HC0 HWB (ms_regs ms4) QC1 QC2 QC4 QC8 QC10 QC21 QC22)
    as (R3 & m3 & C1 & C2 & CK & C34 & HQ' & HIG & Hb0 & Hbmp & HCfr & HCgr).
  replace (SPq + 16) with SP in C2 by (clear - ESPq; lia).
  (* [comment removed for export] *)
  assert (Hn66 : (s_next S <= s_next (hand_post L1p 0x73c38 K34 [0%nat; 2%nat]))%positive) by (cbn [hand_post s_next]; clear - Hn1p; lia).
  assert (HwL2p : state_wf L2p = true).
  { unfold L2p. apply fix_post_wf.
    - unfold L2, ecall_tpl. apply with_regs_wf; [exact (hand_post_wf L1p _ _ _ HwL1p)|].
      repeat (constructor; [split; [intros Hc0; vm_compute in Hc0; discriminate | cbn [fst snd]; first [exact (lwf_mono' _ _ _ Hn66 Hwfa) | apply lwf_lconst]] |]). constructor.
    - unfold L2, ecall_tpl. rewrite with_regs_next. exact (lwf_mono' _ _ _ Hn66 Hwfa). }
  assert (Pw4 : nth_error (s_rgs L2p) 0 = Some (RG (laddc SPl (-2064)) (lconst 2064) RW TEmpty)) by (rewrite Efr2p; reflexivity).
  assert (Pst4 : nth_error (s_rgs L2p) 2 = Some (RG (laddc (p_tg a) 2872) (lconst 16) RW TEmpty)) by (rewrite Efr2p; reflexivity).
  assert (Esp2 : uE E2 SPl = SP) by exact (uE_agree (s_next S) E E2 _ HwSP Ha13).
  assert (Est2 : uE E2 (laddc (p_tg a) 2872) = TT + 2872) by (rewrite (uE_agree (s_next S) E E2 _ (lwf_laddc _ _ _ HwTG) Ha13); exact Est).
  set (OWN_C := fun x : Z => FAv <= x < FAv + 262144 \/ SHFv <= x < SHFv + 32768 \/ owned_C CA SB c x \/ CA - 128 <= x < CA - 128 + 32 \/ RBv <= x < RBv + 32).
  assert (HCsp : 2064 <= uE E2 SPl <= 2^47) by (rewrite Esp2; clear - HSPr; lia).
  assert (HCst : uE E2 (laddc (p_tg a) 2872) + 16 <= 2^47) by (rewrite Est2; clear - B0; lia).
  assert (Hvown2 : forall x, VOWN x -> own_pt E2 M4 x /\ outside E2 (s_rgs (mrg L2p Sp)) (wa x) /\ ~ frz_pt E2 M4 x).
  { intros x Hv. destruct (Hvown x Hv) as ((p & Hp & Hpw) & V2 & V3). split; [|split].
    - exists p. split; [exact (Hsub4 p Hp)|].
      pose proof (sm_wf_own _ M HwfM) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw p Hp) as [Hf1 Hf2]. cbn [L nq_front s_next] in Hf1, Hf2.
      rewrite (uE_agree (s_next S) E E2 _ Hf1 Ha13), (uE_agree (s_next S) E E2 _ Hf2 Ha13). exact Hpw.
    - exact (Hout2 x V2).
    - intros Hf. apply V3. apply (proj1 (frz_pt_agree (s_next L) E E1 M x HwfM Ha1)).
      exact (proj1 (frz_pt_agree (s_next L1p) E1 E2 M2 x HwfM2 Ha3) Hf). }
  assert (HCown : forall x, 0 <= x < 2^64 -> OWN_C x -> own_pt E2 M4 x /\ outside E2 (s_rgs (mrg L2p Sp)) (wa x) /\ ~ frz_pt E2 M4 x).
  { intros x Hx [HO1|[HO1|[HO1|[HO1|HO1]]]].
    - split; [|split].
      + exists (l_fa a c, lconst 262144). split; [cbn [M4 with_own sm_own]; apply in_or_app; right; left; reflexivity|].
        cbn [fst snd]. rewrite Eu2, uE_lc by (clear; lia). exact HO1.
      + exact (Hout2 x (Hvout x ltac:(clear - HO1; lia))).
      + intros Hf. apply (Hc2frz x Hf). rewrite Eu2. exact HO1.
    - apply Hvown2. unfold VOWN. rewrite ESHFv in HO1. right. right. right. exact HO1.
    - apply Hvown2. unfold VOWN. unfold owned_C in HO1. destruct HO1 as [HO1|[HO1|HO1]]; [left; clear - HO1 Hcr; lia | right; left; clear - HO1 Hcr; lia | left; clear - HO1; lia].
    - apply Hvown2. unfold VOWN. left. clear - HO1. lia.
    - split; [|split].
      + exists (l_rb a c, lconst 262144). split; [cbn [M4 M2 with_own sm_own]; apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
        cbn [fst snd]. rewrite (uE_agree (s_next S) E E2 _ Hwrb Ha13), Erb, uE_lc by (clear; lia). clear - HO1. lia.
      + exact (Hout2 x (Hvout x ltac:(clear - HO1; lia))).
      + intros Hf. assert (Hw1 : frz_pt E1 M x) by exact (proj1 (frz_pt_agree (s_next L1p) E1 E2 M2 x HwfM2 Ha3) Hf).
        assert (Hw0 : frz_pt E M x) by exact (proj1 (frz_pt_agree (s_next L) E E1 M x HwfM Ha1) Hw1).
        exact (pg_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x (HinPG x ltac:(left; clear - HO1; lia)) Hw0). }
  assert (HCfr' : forall x, 0 <= x < 2^64 -> ~ (uE E2 SPl - 2064 <= x < uE E2 SPl) ->
            ~ (uE E2 (laddc (p_tg a) 2872) <= x < uE E2 (laddc (p_tg a) 2872) + 16) -> ~ OWN_C x -> m3 (wa x) = mC0' (wa x)).
  { intros x Hx Hw Hs HO1. rewrite Esp2 in Hw. rewrite Est2 in Hs. apply (HCfr x Hx).
    - clear - Hw ESPq. lia.
    - intros Hc0. apply HO1. right. left. exact Hc0.
    - clear - Hs. lia.
    - intros Hc0. apply HO1. left. exact Hc0.
    - intros Hc0. apply HO1. right. right. left. exact Hc0.
    - intros Hc0. apply HO1. right. right. right. left. exact Hc0.
    - intros Hc0. apply HO1. right. right. right. right. exact Hc0. }
  rewrite <- Epc4 in C1.
  apply (den_run_app_x cfg LIMIT model0 Hwx _ L2p Sp E2 M4 ms4 model4 T SPl (laddc (p_tg a) 2872) 0%nat 2%nat TEmpty TEmpty 0x43d4c K34
           [3; 4]%nat R3 m3 OWN_C 2064 ltac:(lia) HDc2 HwL2p eq_refl Pw4 Pst4 HCsp HCst k34_cases C1 C34 HCown HCfr' HCgr).
  intros E3 ms5 model5 HD5 Ha5 Hfz5 Hrr5 Hvis5 HH5 Hrm5.
  (* [comment removed for export] *)
  set (Lh3 := hand_post L2p 0x43d4c K34 [0%nat; 2%nat]) in *.
  set (X := mrg (hand_post Lb 0x43d4c KALLk [0%nat; 2%nat]) Sp) in *.
  assert (En : s_next L2p = s_next Lb).
  { unfold L2p, fix_post. cbn [s_next]. unfold L2, ecall_tpl. rewrite with_regs_next. unfold hand_post. cbn [s_next].
    unfold L1p, fix_post. cbn [s_next]. unfold L1, ecall_tpl. rewrite with_regs_next. cbn [hand_post L Lb nq_front s_next]. clear. lia. }
  assert (Ha35 : agree (s_next S) E E3).
  { apply (agree_trans _ E E2 E3); [exact Ha13|]. apply (agree_mono _ (s_next L2p)); [rewrite En; cbn [Lb nq_front s_next]; clear; lia | exact Ha5]. }
  assert (Hagr3 : forall E'', agree (s_next (mrg Lh3 Sp)) E3 E'' -> agree (s_next S) E E'').
  { intros E'' Ha''. apply (agree_trans _ E E3 E''); [exact Ha35|].
    apply (agree_mono _ (s_next (mrg Lh3 Sp))); [cbn [mrg Lh3 hand_post s_next]; rewrite En; cbn [Lb nq_front s_next]; clear; lia | exact Ha'']. }
  assert (Hregs0 : forall r : reg, getr regs r = lden E (rget (s_regs S) (rkey r))).
  { intros r. destruct Hd10 as (_ & _ & _ & HR0 & _). exact (HR0 r). }
  assert (HwS31 : regs_wf_n (s_next S) (s_regs S) 31 = true).
  { pose proof CwL as X0. unfold state_wf in X0. apply andb_prop in X0 as [X0 _]. apply andb_prop in X0 as [X0 _]. apply andb_prop in X0 as [X0 _]. exact X0. }
  assert (HK34sub : forall key, existsb (Pos.eqb key) KALLk = false -> existsb (Pos.eqb key) K34 = false).
  { intros key Hk0. destruct (existsb (Pos.eqb key) K34) eqn:E34; [|reflexivity]. exfalso.
    apply existsb_exists in E34 as (k0 & Hk1 & Hk2). apply Pos.eqb_eq in Hk2. subst k0.
    assert (HinK : existsb (Pos.eqb key) KALLk = true).
    { apply existsb_exists. exists key. split; [|apply Pos.eqb_refl]. unfold K34 in Hk1. cbn [List.map In] in Hk1. unfold KALLk. cbn [List.map In].
      destruct Hk1 as [<-|[<-|[]]]; [right; right; left; reflexivity | right; right; right; left; reflexivity]. }
    rewrite HinK in Hk0. discriminate. }
  assert (HDX0 : DEN ASEGS LIMIT model0 (ms_mem ms5) E3 (with_regs_t (mrg Lh3 Sp) (s_regs X)) M4 ms5 model5).
  { apply den_regs_eq; [exact HD5|]. intros E'' Ha'' r.
    pose proof (dn_sden _ _ _ _ _ _ _ _ _ HD5 E'' Ha'') as (_ & _ & _ & Hregs & _).
    destruct (bv_eq_dec 5 r (0%bv : reg)) as [->|Hr0]; [reflexivity|].
    destruct (rkey_succ r Hr0) as (kk & Hkk & Ekey).
    rewrite <- (Hregs r). cbn [restrict ms_regs]. rewrite Hrr5.
    unfold X. cbn [s_regs mrg].
    - unfold hand_post at 1. cbn [s_regs].
      rewrite Ekey. rewrite hregs_get by (first [rewrite SuccNat2Pos.id_succ; clear - Hkk; lia | intros Hc0; apply (f_equal Pos.to_nat) in Hc0; rewrite SuccNat2Pos.id_succ in Hc0; cbn in Hc0; clear - Hc0 Hkk; lia]).
      rewrite <- Ekey.
      destruct (existsb (Pos.eqb (rkey r)) KALLk) eqn:EKa.
      + (* [comment removed for export] *)
        cbn [Lb nq_front s_regs].
        rewrite Ekey. rewrite (lden_agree_wf (s_next S) E E'' _ (regs_wf_n_get _ _ 31 HwS31 kk Hkk) (Hagr3 E'' Ha'')). rewrite <- Ekey.
        rewrite <- (Hregs0 r). destruct (kall_cases r EKa) as (k & Hk' & ->).
        cbn [In] in Hk'. destruct Hk' as [<-|[<-|[<-|[<-|Hk']]]].
        * symmetry. exact (CK 1%nat ltac:(cbn [In]; auto 20)).
        * rewrite C2. exact R2.
        * rewrite (C34 3%nat ltac:(left; reflexivity)), Ereg4, getr_rupd_other by regne. rewrite B9, Ereg2, getr_rupd_other by regne.
          symmetry. exact (A8 3%nat ltac:(left; reflexivity)).
        * rewrite (C34 4%nat ltac:(right; left; reflexivity)), Ereg4, getr_rupd_other by regne. rewrite B8. exact R4.
        * symmetry. apply CK. cbn [In]. clear - Hk'. cbn [In] in Hk'. intuition.
      + (* [comment removed for export] *)
        pose proof (Hregs r) as X2. cbn [restrict ms_regs mrg s_regs] in X2. rewrite Hrr5 in X2. unfold Lh3, hand_post in X2. cbn [s_regs] in X2.
        rewrite Ekey in X2. rewrite hregs_get in X2 by (first [rewrite SuccNat2Pos.id_succ; clear - Hkk; lia | intros Hc0; apply (f_equal Pos.to_nat) in Hc0; rewrite SuccNat2Pos.id_succ in Hc0; cbn in Hc0; clear - Hc0 Hkk; lia]).
        rewrite <- Ekey in X2. rewrite (HK34sub _ EKa) in X2. rewrite X2, En. reflexivity. }
  assert (Efc2p : s_facts L2p = []).
  { unfold L2p, fix_post. cbn [s_facts]. unfold L2, ecall_tpl. rewrite with_regs_facts. unfold hand_post. cbn [s_facts].
    unfold L1p, fix_post. cbn [s_facts]. unfold L1, ecall_tpl. rewrite with_regs_facts. reflexivity. }
  assert (EX : with_regs_t (mrg Lh3 Sp) (s_regs X) = X).
  { unfold X at 2. unfold with_regs_t, mrg, Lh3, hand_post. cbn [s_pc s_regs s_rgs s_facts s_next s_resv].
    rewrite Efr2p, Efc2p, En. cbn [Lb nq_front s_rgs s_facts]. rewrite Efront. reflexivity. }
  rewrite EX in HDX0.
  (* [comment removed for export] *)
  assert (HG1 : forall x, 0 <= x < 2^64 -> Hof E M model (wa x) = false -> H2 (wa x) = false -> ~ (RBv <= x < RBv + 262144) -> mB0' (wa x) = mA (wa x)).
  { intros x Hx V0 V2 Hnr. rewrite EmB0. unfold mrestrict. rewrite V2. rewrite fresh_mem_out; [exact (Hvis1 _ V0)|].
    change (Z_to_bv 64 262144) with (wa 262144). rewrite !u_wa_small by (first [exact Hx | unfold RBv; clear - B0 Hcr; lia | clear; lia]). exact Hnr. }
  assert (HG2 : forall x, 0 <= x < 2^64 -> H2 (wa x) = false -> H4 (wa x) = false -> ~ (FAv <= x < FAv + 262144) -> mC0' (wa x) = mB (wa x)).
  { intros x Hx V2 V4 Hnr. rewrite EmC0. unfold mrestrict. rewrite V4. rewrite fresh_mem_out; [exact (Hvis3 _ V2)|].
    change (Z_to_bv 64 262144) with (wa 262144). rewrite !u_wa_small by (first [exact Hx | unfold FAv; clear - B0 Hcr; lia | clear; lia]). exact Hnr. }
  assert (HvisM : forall w, own_pt E M w -> Hof E M model (wa w) = false /\ H2 (wa w) = false /\ H4 (wa w) = false).
  { intros w (p & Hp & Hpw). pose proof (sm_wf_own _ M HwfM) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw p Hp) as [Hf1 Hf2]. cbn [L nq_front s_next] in Hf1, Hf2.
    split; [exact (proj1 (dn_own _ _ _ _ _ _ _ _ _ Hd1 p Hp w Hpw))|]. split.
    - refine (proj1 (dn_own _ _ _ _ _ _ _ _ _ HDc1 p (Hsub2 p Hp) w _)). rewrite (uE_agree (s_next S) E E1 _ Hf1 Ha1), (uE_agree (s_next S) E E1 _ Hf2 Ha1). exact Hpw.
    - refine (proj1 (dn_own _ _ _ _ _ _ _ _ _ HDc2 p (Hsub4 p Hp) w _)). rewrite (uE_agree (s_next S) E E2 _ Hf1 Ha13), (uE_agree (s_next S) E E2 _ Hf2 Ha13). exact Hpw. }
  assert (HvisRB : forall x, RBv <= x < RBv + 262144 -> H2 (wa x) = false /\ H4 (wa x) = false).
  { intros x Hx. split.
    - refine (proj1 (dn_own _ _ _ _ _ _ _ _ _ HDc1 (l_rb a c, lconst 262144) _ x _)); [cbn [M2 with_own sm_own]; apply in_or_app; right; left; reflexivity|].
      cbn [fst snd]. rewrite Eu1, uE_lc by (clear; lia). exact Hx.
    - refine (proj1 (dn_own _ _ _ _ _ _ _ _ _ HDc2 (l_rb a c, lconst 262144) _ x _)); [cbn [M4 M2 with_own sm_own]; apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
      cbn [fst snd]. rewrite (uE_agree (s_next S) E E2 _ Hwrb Ha13), Erb, uE_lc by (clear; lia). exact Hx. }
  (* [comment removed for export] *)
  destruct HFB as [HFB1 HFB2]. fold SHv in HFB1. rewrite ESHv in HFB1. fold SHFv in HCfr. rewrite ESHFv in HCfr. fold RIv in HFB1.
  assert (Hzero5 : forall x, RBv + 32 <= x < RBv + 262144 -> ms_mem ms5 (wa x) = Some (Z_to_bv 8 0)).
  { intros x Hx. destruct (HvisRB x ltac:(clear - Hx; lia)) as [V2 V4]. assert (Hx64 : 0 <= x < 2^64) by (unfold RBv in Hx; clear - Hx B0 Hcr; lia).
    rewrite (Hvis5 _ V4). rewrite (HCfr x Hx64).
    2:{ unfold RBv in Hx. clear - Hx B0 BP Hcr HSPr ESPq. lia. }
    2:{ unfold RBv in Hx. clear - Hx S1 B0 Hcr. lia. }
    2:{ unfold RBv in Hx. clear - Hx Hdisj B0 Hcr. unfold PG_SIZE in Hdisj. fold TT in Hdisj. lia. }
    2:{ unfold RBv, FAv in *. clear - Hx. lia. }
    2:{ unfold owned_C. unfold RBv in Hx. clear - Hx T1 B0 Hcr. lia. }
    2:{ unfold RBv in Hx. clear - Hx T1 B0 Hcr. lia. }
    2:{ unfold RBv in *. clear - Hx. lia. }
    exact (HzeroC x ltac:(clear - Hx; lia)). }
  (* [comment removed for export] *)
  set (hyb := hyb_p (fuc_b CA SB SH c) (ms_mem ms5) mem0).
  assert (Hhyb_in : forall x, 0 <= x < 2^64 -> fuc CA SB SH c x -> hyb (wa x) = ms_mem ms5 (wa x)).
  { intros x Hx Hn. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx. rewrite (proj2 (fuc_b_spec _ _ _ _ _) Hn). reflexivity. }
  assert (Hhyb_out : forall x, 0 <= x < 2^64 -> ~ fuc CA SB SH c x -> hyb (wa x) = mem0 (wa x)).
  { intros x Hx Hn. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx.
    destruct (fuc_b CA SB SH c x) eqn:Eb; [exfalso; apply Hn; apply fuc_b_spec; exact Eb | reflexivity]. }
  assert (Hfuc_v : forall x, fuc CA SB SH c x -> VOWN x \/ RBv <= x < RBv + 262144 \/ FAv <= x < FAv + 262144).
  { intros x Hx. unfold fuc in Hx. unfold VOWN, RBv, FAv. clear - Hx. lia. }
  (* [comment removed for export] *)
  assert (Hfrz0 : forall w, frz_pt E M w -> 0 <= w < 2^64 /\ ~ fuc CA SB SH c w).
  { intros w Hfw. pose proof Hfw as (q & Hq & Hqw). destruct (dn_frz _ _ _ _ _ _ _ _ _ Hd q Hq w Hqw) as (Ht & _ & _).
    pose proof (alloc_top_lo _ (proj1 (dn_spok _ _ _ _ _ _ _ _ _ Hd))) as Hlo. split; [clear - Ht Hlo; lia|].
    intros Hc0. destruct (Hfuc_v w Hc0) as [Hv|Hv].
    - destruct (Hvown w Hv) as (_ & _ & V3). exact (V3 Hfw).
    - exact (pg_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne w (HinPG w Hv) Hfw). }
  assert (Hfrz5 : forall w, frz_pt E M w -> ms_mem ms5 (wa w) = mem0 (wa w)).
  { intros w Hfw. destruct (Hfrz0 w Hfw) as [Hw Hnf].
    assert (Hf1 : frz_pt E1 M2 w) by exact (proj2 (frz_pt_agree (s_next L) E E1 M w HwfM Ha1) Hfw).
    assert (Hf2 : frz_pt E2 M4 w) by exact (proj2 (frz_pt_agree (s_next L1p) E1 E2 M2 w HwfM2 Ha3) Hf1).
    unfold wa. rewrite (Hfz5 w Hf2). change (Z_to_bv 64 w) with (wa w).
    rewrite mem0_z_out by (first [exact Hw | intros Hc0; apply Hnf; unfold fuc; unfold FAv in Hc0; clear - Hc0; lia]).
    unfold wa. rewrite (Hfz3 w Hf1). change (Z_to_bv 64 w) with (wa w).
    rewrite mem0_z_out by (first [exact Hw | intros Hc0; apply Hnf; unfold fuc; unfold RBv in Hc0; clear - Hc0; lia]).
    exact (Hfz1 w Hfw). }
  (* [comment removed for export] *)
  assert (Hnwin : forall w, outside E (s_rgs (mrg L Sp)) (wa w) -> 0 <= w < 2^64 -> ~ (SP - 2064 <= w < SP) /\ ~ (TT + 2872 <= w < TT + 2888)).
  { intros w Hout Hw. unfold outside in Hout. rewrite Forall_forall in Hout. cbn [mrg s_rgs L nq_front] in Hout.
    pose proof (Hout _ (in_or_app _ _ _ (or_introl (nth_error_In _ _ Pw)))) as O1.
    pose proof (Hout _ (in_or_app _ _ _ (or_introl (nth_error_In _ _ Pst)))) as O2.
    cbn [rg_base] in O1, O2. unfold rsz in O1, O2. cbn [rg_size] in O1, O2. rewrite lden_lconst in O1, O2.
    rewrite (u_small64 2064) in O1 by (unfold two64; lia). rewrite (u_small64 16) in O2 by (unfold two64; lia).
    rewrite Ebw in O1. fold (uE E (laddc (p_tg a) 2872)) in O2. rewrite Est in O2. rewrite u_wa_small in O1, O2 by exact Hw. clear - O1 O2. lia. }
  (* [comment removed for export] *)
  assert (Hkeep : forall w, 0 <= w < 2^64 -> own_pt E M w -> outside E (s_rgs (mrg L Sp)) (wa w) -> ~ VOWN w -> ms_mem ms5 (wa w) = mem0 (wa w)).
  { intros w Hw Hm Hout Hnv. destruct (HvisM w Hm) as (V0 & V2 & V4). destruct (Hnwin w Hout Hw) as [Nw Ns].
    destruct (virgin_not_own LIMIT model0 mem0 E S M ms model a Hd HA0 Hne Hown_eq c Hcin Z0 w Hm) as [N1 N2]. fold pz SB in N1, N2. fold RBv in N1. fold FAv in N2.
    rewrite (Hvis5 _ V4). rewrite (HCfr w Hw).
    2:{ clear - Nw ESPq. lia. }
    2:{ intros Hc0. apply Hnv. unfold VOWN. right. right. right. exact Hc0. }
    2:{ exact Ns. }
    2:{ exact N2. }
    2:{ intros Hc0. apply Hnv. unfold VOWN. unfold owned_C in Hc0. clear - Hc0 Hcr. lia. }
    2:{ intros Hc0. apply Hnv. unfold VOWN. left. clear - Hc0. lia. }
    2:{ intros Hc0. apply N1. clear - Hc0. lia. }
    rewrite (HG2 w Hw V2 V4 N2). rewrite (HFB1 w Hw).
    2:{ clear - Nw ESPq. lia. }
    2:{ intros Hc0. apply Hnv. unfold VOWN. right. right. left. exact Hc0. }
    2:{ intros Hc0. apply Hnv. unfold VOWN. unfold RIv in Hc0. clear - Hc0 Hcr. lia. }
    2:{ intros Hc0. apply Hnv. unfold VOWN. clear - Hc0. lia. }
    2:{ exact Ns. }
    rewrite (HG1 w Hw V0 V2 N1). rewrite (A11 w Hw).
    2:{ clear - Nw ESPq. lia. }
    2:{ intros i Hi Hc0. apply Hnv. unfold VOWN. clear - Hc0 Hi. lia. }
    2:{ intros Hc0. apply Hnv. unfold VOWN. unfold RIv in Hc0. clear - Hc0 Hcr. lia. }
    unfold mr. cbn [restrict ms_mem]. unfold mrestrict. rewrite V0.
    destruct Hm as (p & Hp & Hpw). exact (proj2 (dn_own _ _ _ _ _ _ _ _ _ Hd1 p Hp w Hpw) Hout). }
  (* [comment removed for export] *)
  assert (HwfM4 : sm_wf (s_next L2p) M4 = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ HDc2).
  assert (Hown4 : forall w, own_pt E3 M4 w -> own_pt E M w \/ RBv <= w < RBv + 262144 \/ FAv <= w < FAv + 262144).
  { intros w Hw. destruct (proj1 (own_pt_agree (s_next L2p) E2 E3 M4 w HwfM4 Ha5) Hw) as (p & Hp & Hpw).
    cbn [M4 M2 with_own sm_own] in Hp. apply in_app_or in Hp as [Hp|[<-|[]]]; [apply in_app_or in Hp as [Hp|[<-|[]]]|].
    - left. exists p. split; [exact Hp|].
      pose proof (sm_wf_own _ M HwfM) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw p Hp) as [Hf1 Hf2]. cbn [L nq_front s_next] in Hf1, Hf2.
      rewrite <- (uE_agree (s_next S) E E2 _ Hf1 Ha13), <- (uE_agree (s_next S) E E2 _ Hf2 Ha13). exact Hpw.
    - right. left. cbn [fst snd] in Hpw. rewrite (uE_agree (s_next S) E E2 _ Hwrb Ha13), Erb, uE_lc in Hpw by (clear; lia). exact Hpw.
    - right. right. cbn [fst snd] in Hpw. rewrite Eu2, uE_lc in Hpw by (clear; lia). exact Hpw. }
  assert (HshX : shape (s_rgs X) = shape (s_rgs (mrg L Sp))).
  { unfold X. cbn [with_reg mrg s_rgs]. unfold hand_post. cbn [s_rgs]. unfold shape. rewrite !map_app. f_equal.
    pose proof (empty_at_shape [0%nat; 2%nat] (s_rgs Lb) 0) as Hs. unfold shape in Hs. exact Hs. }
  assert (HD6 : DEN ASEGS LIMIT model0 hyb E3 X M4 ms5 model5).
  { apply (den_snap ASEGS LIMIT model0 (ms_mem ms5) hyb E3 X M4 ms5 model5 HDX0).
    - intros w Hw.
      assert (Hf2 : frz_pt E2 M4 w) by exact (proj1 (frz_pt_agree (s_next L2p) E2 E3 M4 w HwfM4 Ha5) Hw).
      assert (Hf1 : frz_pt E1 M2 w) by exact (proj1 (frz_pt_agree (s_next L1p) E1 E2 M2 w HwfM2 Ha3) Hf2).
      assert (Hf0 : frz_pt E M w) by exact (proj1 (frz_pt_agree (s_next L) E E1 M w HwfM Ha1) Hf1).
      destruct (Hfrz0 w Hf0) as [Hw6 Hnf]. change (Z_to_bv 64 w) with (wa w). rewrite (Hhyb_out w Hw6 Hnf). symmetry. exact (Hfrz5 w Hf0).
    - intros w Hw Hout. change (Z_to_bv 64 w) with (wa w).
      destruct (Hown4 w Hw) as [Hm|Hr].
      + assert (Hw6 : 0 <= w < 2^64) by (pose proof (Hw64 w Hm) as X0; unfold two64 in X0; exact X0).
        destruct (fuc_b CA SB SH c w) eqn:Eb; [apply fuc_b_spec in Eb; exact (Hhyb_in w Hw6 Eb)|].
        assert (Hnf : ~ fuc CA SB SH c w) by (intros Hc0; apply fuc_b_spec in Hc0; congruence).
        rewrite (Hhyb_out w Hw6 Hnf). symmetry. apply (Hkeep w Hw6 Hm).
        * exact (outside_agree_shape (s_next L) E E3 _ _ _ HbwS Ha35 HshX Hout).
        * intros Hv. apply Hnf. unfold fuc. unfold VOWN in Hv. clear - Hv. lia.
      + apply Hhyb_in; [unfold RBv, FAv in Hr; clear - Hr B0 Hcr; lia | unfold fuc; unfold RBv, FAv in Hr; clear - Hr; lia]. }
  (* [comment removed for export] *)
  pose proof (den_uncarve ASEGS LIMIT model0 hyb E3 X M4 ms5 model5 _ _ l'' HD6 CpX Hsteps) as HD7.
  (* [comment removed for export] *)
  assert (Hv4f : forall x, fuc CA SB SH c x -> H4 (wa x) = false).
  { intros x Hx. destruct (Hfuc_v x Hx) as [Hv|[Hr|Hf]].
    - apply Hcov4. right. right. right. exact Hv.
    - exact (proj2 (HvisRB x Hr)).
    - refine (proj1 (dn_own _ _ _ _ _ _ _ _ _ HDc2 (l_fa a c, lconst 262144) _ x _)); [cbn [M4 with_own sm_own]; apply in_or_app; right; left; reflexivity|].
      cbn [fst snd]. rewrite Eu2, uE_lc by (clear; lia). exact Hf. }
  assert (Hfuc64 : forall x, fuc CA SB SH c x -> 0 <= x < 2^64).
  { intros x Hx. destruct (Hvf x Hx) as (_ & _ & F4). clear - F4. lia. }
  assert (Hhyb_m3 : forall x, fuc CA SB SH c x -> hyb (wa x) = m3 (wa x)).
  { intros x Hx. rewrite (Hhyb_in x (Hfuc64 x Hx) Hx). exact (Hvis5 _ (Hv4f x Hx)). }
  destruct HPB as (PBsh & PBrest). fold SHv in PBsh. rewrite ESHv in PBsh.
  assert (Hfa3 : forall x, SH + 536870912 * c <= x < SH + 536870912 * c + 32768 -> m3 (wa x) = Some (Z_to_bv 8 250)).
  { intros x Hx. assert (Hv : VOWN x) by (unfold VOWN; right; right; left; exact Hx).
    assert (Hx64 : 0 <= x < 2^64) by (apply Hfuc64; unfold fuc; clear - Hx; lia).
    rewrite (HCfr x Hx64).
    2:{ clear - Hx S3 HSPr ESPq Hcr. lia. }
    2:{ clear - Hx. lia. }
    2:{ clear - Hx Hnsh S1 S3 Hcr. lia. }
    2:{ unfold FAv. clear - Hx S1 B0 Hcr. lia. }
    2:{ unfold owned_C. clear - Hx S1 S3 B0 Hcr Hnsh. lia. }
    2:{ clear - Hx S1 S3 B0 Hcr Hnsh. lia. }
    2:{ unfold RBv. clear - Hx S1 B0 Hcr. lia. }
    rewrite (HG2 x Hx64 (Hcov2 x ltac:(right; right; right; exact Hv)) (Hcov4 x ltac:(right; right; right; exact Hv)) ltac:(unfold FAv; clear - Hx S1 B0 Hcr; lia)).
    exact (PBsh x Hx). }
  set (SHs := SH + 536870912 * c).
  (* [comment removed for export] *)
  assert (Bz1 : 0 <= CA /\ CA + 4096 <= 2^63 /\ 0 <= SB /\ SB + 137438953472 + 4096 <= 2^63) by (clear - B0; lia).
  assert (HIo' : INV_Co hyb CA SB c (sz_tbl c) (mc_tbl c / 2) (262144 / sz_tbl c) (z_j pz c + 1)).
  { rewrite Hj0. change (0 + 1) with 1.
    apply (INV_Co_frame m3); [clear - Bz1; lia | clear - Bz1; lia | clear - Bz1; lia | clear - Bz1; lia | | exact (INV_G_o _ _ _ _ _ _ _ _ HIG)].
    intros x Hf. apply Hhyb_m3. unfold foot_Co in Hf. unfold fuc. clear - Hf Hcr Hnw. lia. }
  destruct PBrest as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PBst2).   (* [comment removed for export] *)
  assert (HST' : STATS hyb CA).
  { apply (STATS_frame m3); [clear - Bz1; lia | clear - Bz1; lia | intros x Hx; apply Hhyb_m3; unfold fuc; clear - Hx; lia|].
    split; [exact (ig_st _ _ _ _ _ _ _ _ HIG)|]. split; [|exact (ig_wst _ _ _ _ _ _ _ _ HIG)].
    assert (Rc : rd mC0' (CA + 2584) 8 (st2 + 262144)).
    { apply (rd_frame mB mC0'); [clear - Bz1; lia | cbn; clear - Bz1; lia | | exact PBst2]. intros x Hx. cbn in Hx.
      assert (Hv : VOWN x) by (unfold VOWN; left; clear - Hx; lia).
      exact (HG2 x ltac:(clear - Hx Bz1; lia) (Hcov2 x ltac:(right; right; right; exact Hv)) (Hcov4 x ltac:(right; right; right; exact Hv)) ltac:(unfold FAv; clear - Hx T1 B0 Hcr; lia)). }
    exact (rd_grows_ex mC0' m3 (CA + 2584) 8 _ ltac:(lia) ltac:(clear - Bz1; lia) ltac:(cbn; clear - Bz1; lia) HCgr Rc). }
  assert (HPo' : POP_C hyb SB SH c (sz_tbl c) (z_j pz c + 1)).
  { rewrite Hj0. constructor.
    - intros x Hx. unfold RBX in Hx. assert (Hxr : RBv <= x < RBv + 262144) by (unfold RBv; clear - Hx Hszp; lia).
      rewrite (Hhyb_in x ltac:(unfold RBv in Hxr; clear - Hxr B0 Hcr; lia) ltac:(unfold fuc; unfold RBv in Hxr; clear - Hxr; lia)).
      exact (Hzero5 x ltac:(unfold RBv; clear - Hx Hszp; lia)).
    - intros x Hx. unfold SHX in Hx. assert (Hxr : SHs <= x < SHs + 32768) by (unfold SHs; clear - Hx Hsz8; lia).
      rewrite (Hhyb_m3 x ltac:(unfold fuc; unfold SHs in Hxr; clear - Hxr; lia)). exact (Hfa3 x Hxr).
    - intros x Hx. unfold SHX in Hx. rewrite (Hhyb_m3 x ltac:(unfold fuc; clear - Hx; lia)), (Hfa3 x Hx). discriminate. }
  (* [comment removed for export] *)
  assert (Hcb_chain : forall x, CA - 128 <= x < CA + 2592 -> ~ owned_C CA SB c x -> ~ (CA - 128 <= x < CA - 96) -> hyb (wa x) = mA (wa x)).
  { intros x Hx Hno Hnq. assert (Hv : VOWN x) by (unfold VOWN; left; exact Hx).
    assert (Hx64 : 0 <= x < 2^64) by (clear - Hx Bz1 HCA'; lia).
    assert (V0 := Hcov0 x ltac:(right; right; right; exact Hv)). assert (V2 := Hcov2 x ltac:(right; right; right; exact Hv)).
    assert (V4 := Hcov4 x ltac:(right; right; right; exact Hv)).
    rewrite (Hhyb_m3 x ltac:(unfold fuc; clear - Hx; lia)). rewrite (HCfr x Hx64).
    2:{ clear - Hx HCA'. lia. }
    2:{ clear - Hx S1 S3 B0 Hcr Hnsh. lia. }
    2:{ intros Hc0. apply Hno. unfold owned_C. clear - Hc0 Hx B0. lia. }
    2:{ unfold FAv. clear - Hx T1 B0 Hcr. lia. }
    2:{ exact Hno. }
    2:{ intros Hc0. apply Hnq. clear - Hc0. lia. }
    2:{ unfold RBv. clear - Hx T1 B0 Hcr. lia. }
    rewrite (HG2 x Hx64 V2 V4 ltac:(unfold FAv; clear - Hx T1 B0 Hcr; lia)). rewrite (HFB1 x Hx64).
    2:{ clear - Hx HCA'. lia. }
    2:{ clear - Hx S1 S3 B0 Hcr Hnsh. lia. }
    2:{ unfold RIv. clear - Hx T1 B0 Hcr. lia. }
    2:{ intros Hc0. apply Hno. unfold owned_C. clear - Hc0. lia. }
    2:{ intros Hc0. apply Hno. unfold owned_C. clear - Hc0 Hx B0. lia. }
    exact (HG1 x Hx64 V0 V2 ltac:(unfold RBv; clear - Hx T1 B0 Hcr; lia)). }
  assert (HWC' : wr hyb (CA - 128) 2720).
  { apply wr_bytes; [clear - Bz1 HCA'; lia | clear - Bz1; lia|]. intros x Hx.
    assert (Hv : VOWN x) by (unfold VOWN; left; clear - Hx; lia).
    assert (Hx64 : 0 <= x < 2^64) by (clear - Hx Bz1 HCA'; lia).
    assert (V0 := Hcov0 x ltac:(right; right; right; exact Hv)). assert (V2 := Hcov2 x ltac:(right; right; right; exact Hv)).
    assert (V4 := Hcov4 x ltac:(right; right; right; exact Hv)).
    pose proof (wr_byte mem0 (CA - 128) 2720 x ltac:(clear - Bz1 HCA'; lia) ltac:(clear - Bz1; lia) (iz_wc _ _ HI) Hx) as Wv0.
    assert (Wv1 : wview SEGS mr (wa x) <> None) by (rewrite (wview_same mem0 mr); [exact Wv0 | apply Hmr_foot; left; clear - Hx; lia]).
    pose proof (wview_grows mr mA x HAgr Wv1) as Wv2.
    assert (Wv3 : wview SEGS mB0' (wa x) <> None) by (rewrite (wview_same mA mB0'); [exact Wv2 | exact (HG1 x Hx64 V0 V2 ltac:(unfold RBv; clear - Hx T1 B0 Hcr; lia))]).
    pose proof (wview_grows mB0' mB x HFB2 Wv3) as Wv4.
    assert (Wv5 : wview SEGS mC0' (wa x) <> None) by (rewrite (wview_same mB mC0'); [exact Wv4 | exact (HG2 x Hx64 V2 V4 ltac:(unfold FAv; clear - Hx T1 B0 Hcr; lia))]).
    pose proof (wview_grows mC0' m3 x HCgr Wv5) as Wv6.
    rewrite (wview_same m3 hyb); [exact Wv6 | apply Hhyb_m3; unfold fuc; clear - Hx; lia]. }
  assert (HICv : forall i, In i CLS -> i <> c ->
            (rd hyb (CA + 80 * i + 4) 4 (mc_tbl i) /\ rd hyb (CA + 80 * i + 8) 8 (sz_tbl i)) \/ (forall x, icc CA i x -> hyb (wa x) = mem0 (wa x))).
  { intros i Hi Hic. pose proof (in_cls_rng i Hi) as Hir.
    assert (Hch : forall x, icc CA i x -> hyb (wa x) = mA (wa x)).
    { intros x Hx. unfold icc in Hx. apply Hcb_chain; [clear - Hx Hir; lia | unfold owned_C; clear - Hx Hir Hic Hcr T1 B0; lia | clear - Hx Hir; lia]. }
    destruct A10 as [A10|A10].
    - left. destruct (A10 i ltac:(clear - Hir; lia)) as [Rm Rs]. split.
      + apply (rd_frame mA hyb); [clear - Bz1 Hir; lia | cbn; clear - Bz1 Hir; lia | intros x Hx; cbn in Hx; apply Hch; unfold icc; clear - Hx; lia | exact Rm].
      + apply (rd_frame mA hyb); [clear - Bz1 Hir; lia | cbn; clear - Bz1 Hir; lia | intros x Hx; cbn in Hx; apply Hch; unfold icc; clear - Hx; lia | exact Rs].
    - right. intros x Hx. rewrite (Hch x Hx). unfold icc in Hx. rewrite (A10 x ltac:(clear - Hx Hir; lia)). apply Hmr_foot. left. clear - Hx Hir. lia. }
  (* [comment removed for export] *)
  assert (Hri_chain : forall x, SB + 137438953472 <= x < SB + 137438953472 + 4096 -> ~ owned_C CA SB c x -> hyb (wa x) = mA (wa x)).
  { intros x Hx Hno. assert (Hv : VOWN x) by (unfold VOWN; right; left; exact Hx).
    assert (Hx64 : 0 <= x < 2^64) by (clear - Hx Bz1; lia).
    assert (V0 := Hcov0 x ltac:(right; right; right; exact Hv)). assert (V2 := Hcov2 x ltac:(right; right; right; exact Hv)).
    assert (V4 := Hcov4 x ltac:(right; right; right; exact Hv)).
    rewrite (Hhyb_m3 x ltac:(unfold fuc; clear - Hx; lia)). rewrite (HCfr x Hx64).
    2:{ clear - Hx HSB'. lia. }
    2:{ clear - Hx S1 S3 B0 Hcr. lia. }
    2:{ clear - Hx Hdisj B0. unfold PG_SIZE in Hdisj. fold TT in Hdisj. lia. }
    2:{ unfold FAv. clear - Hx Hcr. lia. }
    2:{ exact Hno. }
    2:{ clear - Hx T1 B0. lia. }
    2:{ unfold RBv. clear - Hx Hcr. lia. }
    rewrite (HG2 x Hx64 V2 V4 ltac:(unfold FAv; clear - Hx Hcr; lia)). rewrite (HFB1 x Hx64).
    2:{ clear - Hx HSB'. lia. }
    2:{ clear - Hx S1 S3 B0 Hcr. lia. }
    2:{ intros Hc0. apply Hno. unfold owned_C. unfold RIv in Hc0. clear - Hc0. lia. }
    2:{ clear - Hx T1 B0. lia. }
    2:{ clear - Hx Hdisj B0. unfold PG_SIZE in Hdisj. fold TT in Hdisj. lia. }
    exact (HG1 x Hx64 V0 V2 ltac:(unfold RBv; clear - Hx Hcr; lia)). }
  assert (HF2 : forall x, pri_foot_z pz x -> ~ owned_C CA SB c x -> (forall i, 1 <= i <= 31 -> i <> c -> ~ icc CA i x) ->
            ~ (SH + 536870912 * c <= x < SH + 536870912 * c + 32768) ->
            ~ (SH + 536870912 * c + 469762048 <= x < SH + 536870912 * c + 469762048 + 32768) ->
            ~ (CA - 128 <= x < CA - 96) -> hyb (wa x) = mem0 (wa x)).
  { intros x Hf Hno Hni Hn5 Hn6 Hnq. pose proof (pri_foot_rng E a mem0 HI x Hf) as Rx.
    assert (Hx64 : 0 <= x < 2^64) by (clear - Rx; lia).
    destruct (fuc_b CA SB SH c x) eqn:Eb; [apply fuc_b_spec in Eb | apply (Hhyb_out x Hx64); intros Hc0; apply fuc_b_spec in Hc0; congruence].
    destruct (foot_not_virgin pz mem0 c HI Hdisj Hcin Z0 x Hf) as [Nrb Nfa]. fold SB in Nrb, Nfa.
    assert (HA11 : mA (wa x) = mr (wa x)).
    { apply (A11 x Hx64).
      - unfold fuc in Eb. clear - Eb Nrb Nfa Hn5 Hn6 HCA' HSB'. lia.
      - intros i Hi Hc0. destruct (Z.eq_dec i c) as [->|Hic]; [apply Hno; unfold owned_C; clear - Hc0; lia | exact (Hni i Hi Hic Hc0)].
      - intros Hc0. apply Hno. unfold owned_C. unfold RIv in Hc0. clear - Hc0. lia. }
    destruct Eb as [Eb|[Eb|Eb]].
    - rewrite (Hcb_chain x Eb Hno Hnq), HA11. apply Hmr_foot. left. exact Eb.
    - rewrite (Hri_chain x Eb Hno), HA11. apply Hmr_foot. right. left. exact Eb.
    - exfalso. clear - Eb Nrb Nfa Hn5 Hn6. lia. }
  (* [comment removed for export] *)
  assert (HQh : q_inv hyb (CA - 128) SB 0 1 (sz + 8192)).
  { apply (q_inv_frame m3); [clear - B0; lia | clear - Bz1; lia | clear - Bz1; lia | clear - Bz1; lia | | | exact HQ'].
    - intros x Hx. apply Hhyb_m3. unfold fuc. clear - Hx. lia.
    - intros _ x Hx. apply Hhyb_m3. unfold fuc. clear - Hx Hc24. lia. }
  (* [comment removed for export] *)
  assert (Hj24 : z_j pz 24 = 0) by (rewrite <- Hc24; exact Hj0).
  assert (Z24 : z_z pz 24 = 0) by (rewrite <- Hc24; exact Z0).
  pose proof HIo' as HIo24. pose proof HPo' as HPo24. pose proof HICv as HICv24. pose proof HF2 as HF24.
  rewrite Hc24 in HIo24, HPo24, HICv24, HF24.
  assert (HIz' : INV_Az (qz_new pz sz) hyb).
  { apply (INV_Az_qnew2 pz mem0 hyb sz HI Hdisj Hqn0 Hj24); [rewrite Hj24; exact HQh | exact HIo24 | exact HPo24 | exact HST' | exact HWC' | exact HICv24 | exact HF24]. }
  (* [comment removed for export] *)
  set (pri' := q_step_new a szl) in *.
  assert (Ha'' : a_qstep a pri' = a_with a pri') by reflexivity.
  set (a' := a_qstep a pri') in *.
  pose proof (iz_len _ _ HI) as Hlenz.
  assert (Epz' : pden E3 a = pz) by exact (pden_agree (s_next S) E E3 a Haw Ha35).
  assert (Hwsz : lwf (s_next S) szl = true) by exact (regs_wf_n_get _ _ 31 HwS31 14%nat ltac:(lia)).
  assert (Epz2 : pden E3 a' = qz_new pz sz).
  { unfold a', pri'. rewrite (pden_qnew E3 a szl Hlen); rewrite ?Epz', ?(uE_agree (s_next S) E E3 szl Hwsz Ha35).
    - reflexivity.
    - rewrite Hj24. unfold two64. clear. lia.
    - fold sz. clear - Hsz40. unfold two64. lia. }
  assert (Hne' : pri' <> []).
  { intros Hn. pose proof (f_equal (@List.length lin) Hn) as XL. unfold pri', q_step_new, pri_step in XL. rewrite !set_nth_length, Hlen in XL. discriminate. }
  assert (Hbase : forall k, (k < 5)%nat -> nth k pri' lc0 = nth k (a_pri a) lc0).
  { intros k Hk5. unfold pri', q_step_new, pri_step, QCLS. change (cidx 24) with 23%nat.
    rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia).
    replace (Nat.eqb k 67) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
    rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia).
    replace (Nat.eqb k 66) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
    rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia).
    replace (Nat.eqb k 65) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
    rewrite nth_set_nth by (rewrite !set_nth_length, Hlen; unfold PRI_LEN; clear; lia).
    replace (Nat.eqb k (6 + 2 * 23)) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia).
    rewrite nth_set_nth by (rewrite Hlen; unfold PRI_LEN; clear; lia).
    replace (Nat.eqb k (5 + 2 * 23)) with false by (symmetry; apply Nat.eqb_neq; clear - Hk5; lia). reflexivity. }
  assert (Hmono : forall x, pri_foot_z (pden E a) x -> pri_foot_z (pden E3 (a_with a pri')) x).
  { intros x Hf. change (a_with a pri') with a'. rewrite Epz2. fold pz in Hf. unfold pri_foot_z in Hf |- *.
    rewrite (qnew_ca pz sz Hlenz), (qnew_sb pz sz Hlenz), (qnew_sh pz sz Hlenz).
    destruct Hf as [Hf|[Hf|[Hf|(c' & Hc' & Hf)]]]; [left; exact Hf | right; left; exact Hf | right; right; left; exact Hf |]. right. right. right. exists c'. split; [exact Hc'|].
    destruct (Z.eq_dec c' 24) as [->|Hnc]; [rewrite (qnew_z24 pz sz Hlenz); rewrite Z24 in Hf; clear - Hf; lia|].
    rewrite (qnew_z_other pz sz Hlenz c' (in_cls_rng c' Hc') Hnc). exact Hf. }
  assert (Hdepf : forall x, 0 <= x < 2^64 -> downed (dD1 E a) (dB1 E a) x -> hyb (wa x) = mem0 (wa x)).
  { intros x Hx Hdw. apply (Hhyb_out x Hx). intros Hn. destruct (Hfuc_v x Hn) as [Hv|Hv].
    - assert (F1 : pri_foot_z pz x).
      { unfold pri_foot_z. fold CA SB SH. unfold VOWN in Hv. destruct Hv as [Hv|[Hv|Hv]]; [left; exact Hv | right; left; exact Hv |].
        right. right. right. exists c. split; [exact Hcin|]. right. right. exact Hv. }
      exact (pri_not_downed LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1 Hdw).
    - pose proof (ha_own _ _ _ _ HA0 x Hx Hdw) as Hod.
      destruct (virgin_not_own LIMIT model0 mem0 E S M ms model a Hd HA0 Hne Hown_eq c Hcin Z0 x Hod) as [N1 N2]. fold pz SB in N1, N2. fold RBv in N1. fold FAv in N2.
      clear - Hv N1 N2. tauto. }
  assert (Hext_step : forall b z, ext_sem (pden E a) b z -> ext_sem (pden E3 (a_with a pri')) b z).
  { intros b z Hbz. change (a_with a pri') with a'. rewrite Epz2. exact (ext_sem_qnew pz mem0 sz HI b z Hbz). }
  (* [comment removed for export] *)
  assert (Hext_fr : forall b z, ext_sem (pden E a) b z -> forall x, b <= x < b + z -> hyb (wa x) = mem0 (wa x)).
  { intros b z Hbz x Hxr. destruct (ext_sem_pt pz mem0 HI b z x Hbz Hxr) as (Rx & Hap & _ & HnQ & HnG).
    apply (Hhyb_out x ltac:(clear - Rx; lia)). intros Hn.
    apply (proj1 (proj2 (Hvf x ltac:(destruct (Hfuc_v x Hn) as [Hv|[Hv|Hv]]; [unfold VOWN in Hv; clear - Hv; tauto | clear - Hv; tauto | clear - Hv; tauto])))). exact Hap. }
  pose proof (HA_pri_step (s_next S) E E3 M a mem0 hyb pri' HA0 Haw Ha35 Hne Hne' Hown_eq
                ltac:(change (a_with a pri') with a'; rewrite Epz2; exact HIz') Hbase Hmono Hdepf Hext_step Hext_fr) as HA'.
  pose proof (own_pt_with (s_next S) E E3 M a mem0 hyb pri' HA0 Haw Ha35 Hne Hown_eq
                ltac:(change (a_with a pri') with a'; rewrite Epz2; exact HIz') Hbase Hmono) as Hsub.
  change (a_with a pri') with a' in HA', Hsub.
  (* [comment removed for export] *)
  set (Y := with_rgs X l'') in *.
  assert (Hnea' : a_pri a' <> []) by exact Hne'.
  pose proof (ha_pri _ _ _ _ HA' Hnea') as HPa'.
  assert (Hfoot_new : forall w, pri_foot_z (qz_new pz sz) w -> pri_foot_z pz w \/ RBv <= w < RBv + 262144 \/ FAv <= w < FAv + 262144).
  { intros w Hf. unfold pri_foot_z in Hf |- *. rewrite (qnew_ca pz sz Hlenz), (qnew_sb pz sz Hlenz), (qnew_sh pz sz Hlenz) in Hf.
    destruct Hf as [Hf|[Hf|[Hf|(c' & Hc' & Hf)]]]; [left; left; exact Hf | left; right; left; exact Hf | left; right; right; left; exact Hf |].
    destruct (Z.eq_dec c' 24) as [->|Hnc].
    - rewrite (qnew_z24 pz sz Hlenz) in Hf. fold SB in Hf. destruct Hf as [Hf|[Hf|Hf]]; [right; left; unfold RBv; clear - Hf Hc24; lia | right; right; unfold FAv; clear - Hf Hc24; lia |].
      left. right. right. right. exists 24. split; [exact in_cls_24|]. right. right. exact Hf.
    - rewrite (qnew_z_other pz sz Hlenz c' (in_cls_rng c' Hc') Hnc) in Hf. left. right. right. right. exists c'. split; [exact Hc' | exact Hf]. }
  assert (Hown_M4 : forall w, own_pt E M w -> own_pt E3 M4 w).
  { intros w (p & Hp & Hpw). exists p. split; [exact (Hsub4 p Hp)|].
    pose proof (sm_wf_own _ M HwfM) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw p Hp) as [Hf1 Hf2]. cbn [L nq_front s_next] in Hf1, Hf2.
    rewrite (uE_agree (s_next S) E E3 _ Hf1 Ha35), (uE_agree (s_next S) E E3 _ Hf2 Ha35). exact Hpw. }
  assert (Hown_maps : forall w, RBv <= w < RBv + 262144 \/ FAv <= w < FAv + 262144 -> own_pt E3 M4 w).
  { intros w [Hr|Hr].
    - exists (l_rb a c, lconst 262144). split; [cbn [M4 M2 with_own sm_own]; apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
      cbn [fst snd]. rewrite (uE_agree (s_next S) E E3 _ Hwrb Ha35), Erb, uE_lc by (clear; lia). exact Hr.
    - exists (l_fa a c, lconst 262144). split; [cbn [M4 with_own sm_own]; apply in_or_app; right; left; reflexivity|].
      cbn [fst snd]. rewrite (uE_agree (s_next S) E E3 _ Hwfa Ha35), Efa, uE_lc by (clear; lia). exact Hr. }
  assert (HD10 : DEN ASEGS LIMIT model0 hyb E3 Y (with_own M (a_own a')) ms5 model5).
  { change (with_own M (a_own a')) with (with_own M4 (a_own a')).
    apply (den_own_set ASEGS LIMIT model0 hyb hyb E3 Y M4 ms5 model5 (a_own a') HD7).
    - apply forallb_forall. intros p Hp. rewrite forallb_forall in Cwo. specialize (Cwo p Hp). apply andb_prop in Cwo as [W1' W2'].
      apply andb_true_intro. split; apply (lwf_mono' (s_next S)); first [assumption | cbn [Y with_rgs X mrg hand_post Lb nq_front s_next]; clear; lia].
    - intros w _. reflexivity.
    - intros w Hw. destruct (Hown4 w Hw) as [Hm|Hr]; [exact (Hsub w Hm)|].
      apply (po_own _ _ _ _ HPa' w); [unfold RBv, FAv in Hr; clear - Hr B0 Hcr; lia|].
      unfold pri_foot. rewrite Epz2. unfold pri_foot_z. rewrite (qnew_ca pz sz Hlenz), (qnew_sb pz sz Hlenz), (qnew_sh pz sz Hlenz).
      right. right. right. exists 24. split; [exact in_cls_24|]. rewrite (qnew_z24 pz sz Hlenz). fold SB. unfold RBv, FAv in Hr. clear - Hr Hc24. lia.
    - intros w (q & Hq & Hqw). cbn [with_own sm_own] in Hq.
      assert (Hw4 : own_pt E3 M4 w).
      { rewrite (ha_aown _ _ _ _ HA') in Hq. unfold aown_of in Hq. apply in_app_or in Hq as [Hq|Hq].
        - apply Hown_M4. exists q. split.
          + rewrite Hown_eq, (ha_aown _ _ _ _ HA0). unfold aown_of. apply in_or_app. left. exact Hq.
          + assert (Hpw : pwf (s_next S) q = true).
            { pose proof Haw as XW. unfold awf in XW. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [_ XW].
              rewrite forallb_forall in XW. apply XW. rewrite (ha_aown _ _ _ _ HA0). unfold aown_of. apply in_or_app. left. exact Hq. }
            unfold pwf in Hpw. apply andb_prop in Hpw as [Hp1 Hp2]. rewrite <- (uE_agree _ E E3 _ Hp1 Ha35), <- (uE_agree _ E E3 _ Hp2 Ha35). exact Hqw.
        - assert (Hq' : In q (pri_own a')) by (change (a_pri a') with pri' in Hq; destruct pri'; [destruct Hq | exact Hq]).
          pose proof (pri_own_foot E3 a' hyb ltac:(unfold INV_A; rewrite Epz2; exact HIz') q Hq' w Hqw) as Hf.
          unfold pri_foot in Hf. rewrite Epz2 in Hf. destruct (Hfoot_new w Hf) as [Hf0|Hr]; [|exact (Hown_maps w Hr)].
          apply Hown_M4. apply (po_own _ _ _ _ HP0 w); [pose proof (pri_foot_rng E a mem0 HI w Hf0) as Rfw; clear - Rfw; lia | exact Hf0]. }
      destruct Hw4 as (q0 & Hq0 & Hq0w). exact (dn_own _ _ _ _ _ _ _ _ _ HD7 q0 Hq0 w Hq0w). }
  apply (Hk E3 hyb ms5 model5).
  - exact Ha35.
  - intros q Hq w Hw. destruct (Hfrz0 w (ex_intro _ q (conj Hq Hw))) as [Hw6 Hnf]. exact (Hhyb_out w Hw6 Hnf).
  - exact HD10.
  - intros _. exact HA'.
Qed.
End NEnqFirst.
(* [comment removed for export] *)
