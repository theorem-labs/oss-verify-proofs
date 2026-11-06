(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
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
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put AXG_put3 AXG_np AXG_npscp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_nf1 AXG_npf AXG_nf6 AXG_gp AXG_gf1 AXG_gf6.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriStep.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_npscp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf2.AXG_nfscp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_npf OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf6 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf6 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep.AXG_gpf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMrg.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcCarve AcSteps AcEntry AcMALp AcHand AcUnwApp0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcDepDen AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcCarveP AcMALlib AcPutN AcUnwApp AcTbl.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcConv AcConvG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriStep AcPriHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcCarveP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChAdd.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcOwnSet AcDenW AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFixNew.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFixXS.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcFixXS.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcDenW.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcCommit.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcNPop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcNPopN.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriStep2 AcNPopF AcNPopG AcNEnqLib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcShapes0.AcPutAppG OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcShapes0.AcShapes OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcShapes0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA.AcLv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCarveP OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPutN OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcTblOk OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvG OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA.AcRdw OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA.AcPriDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCarveP.AcStepsOut OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd.AcAddOwn OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcOwnSet OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFixNew.AcFixS OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFixXS.AcFixX OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFixXS OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDenW.AcRegsEq OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCommit OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep.AcRunApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep.AcNPopApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNPopN OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriHA.AcPriGrant OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcShapes0.AcStateWf OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep2 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNPopF OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNPopG OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNEnqLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcNPopGLib.
Import ListNotations.

Module AcNPopGN.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChFix FxChEnt FxWvC FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put AXG_put3 AXG_np AXG_nf1 AXG_npf AXG_gp AXG_gf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriStep.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put3 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_npf OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_gf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep.AXG_gpf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMrg.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcCarve AcSteps AcEntry AcMALp AcHand AcUnwApp0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcDepDen AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcCarveP AcMALlib AcPutN AcUnwApp AcTbl.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcConv AcConvG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriStep AcPriHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcCarveP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChAdd.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcOwnSet AcDenW AcConvA AcNPop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcNPopN AcNPopG.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcShapes0.AcPutAppG OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcShapes0.AcShapes OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcShapes0 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA.AcLv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCarveP OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPutN OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcUnwApp.AcTblOk OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConv OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvG OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA.AcRdw OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA.AcPriDen OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcCarveP.AcStepsOut OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd.AcAddOwn OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcOwnSet OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPriStep.AcNPopApp OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNPopN OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcNPopG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcNPopGLib.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NPopGNode.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.

#[using="Hwx"] Theorem npopg_node_pop : forall S M a S' M' a', apost_npopg0 LIMIT S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  1 <= z_j (pden E a) (cls_of (uE E (rget (s_regs S) (rk 12)))) ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hj1 Hk.
  unfold apost_npopg0 in H. cbv zeta in H.
  apply obool_some in H as (Hon & H).
  apply obind_some in H as (ND8 & Hnd8 & H). cbv beta in H.
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
  apply andb_prop in Hchk as [Hchk Cfu]. apply andb_prop in Hchk as [Hchk Csep]. apply andb_prop in Hchk as [Hchk Cawf].
  apply andb_prop in Hchk as [Hchk CpX]. apply andb_prop in Hchk as [Hchk CwLg]. apply andb_prop in Hchk as [Hchk CwL].
  apply andb_prop in Hchk as [Hchk Cband]. apply andb_prop in Hchk as [Hchk Cge]. apply andb_prop in Hchk as [Hchk Cjb].
  apply andb_prop in Hchk as [Hchk Csbw]. apply andb_prop in Hchk as [Hchk Cst]. apply andb_prop in Hchk as [Hchk Cro].
  apply andb_prop in Hchk as [Hchk Cwin]. apply andb_prop in Hchk as [Hchk Csphi]. apply andb_prop in Hchk as [Hchk Csplo].
  apply andb_prop in Hchk as [Hchk Cmod]. apply andb_prop in Hchk as [Hchk Cchi]. apply andb_prop in Hchk as [Hchk Cclohi].
  apply andb_prop in Hchk as [Hchk Cclo1]. apply andb_prop in Hchk as [Hchk Cnd8]. apply andb_prop in Hchk as [Hchk Cndhi]. apply andb_prop in Hchk as [Hchk Cndlo].
  apply andb_prop in Hchk as [Hchk Ca3]. apply andb_prop in Hchk as [Hchk Ca1]. apply andb_prop in Hchk as [Cperm Ca0].
  apply lin_eqb_eq in Ca0, Ca1, Ca3. apply Z.leb_le in Cndlo, Cndhi, Cnd8, Cclo1, Cclohi, Cchi, Csplo, Csphi.
  set (SPl := rget (s_regs S) (rk 2)) in *. set (ndl := rget (s_regs S) (rk 12)) in *.
  set (front := firstn 3 (carve_rgs cv)) in *. set (rest := skipn 3 (carve_rgs cv)) in *.
  set (L := np_front S (s_next S) front) in *. set (Sp := np_rest S rest) in *.
  set (n0 := (s_next S + 1)%positive) in *.
  set (Lb := np_front S (n0 + 66) front) in *.
  set (clo := tcls (fst (irange (s_facts S) ndl))) in *. set (chi := tcls (snd (irange (s_facts S) ndl))) in *. set (cs := crange clo chi) in *.
  pose proof (HHA Hon) as HA0.
  assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hlen; discriminate).
  pose proof (ha_pri _ _ _ _ HA0 Hne) as HP0.
  (* [comment removed for export] *)
  pose proof (den_carve ASEGS LIMIT model0 mem0 E S M ms model _ _ _ cv Hd Hcv Cperm) as Hd1.
  assert (EQ1 : with_rgs S (carve_rgs cv) = mrg L Sp).
  { destruct S as [pc0 rg0 rgs0 fs0 nx0 rv0]. cbn [s_pc s_resv] in Hpc, Hrs. subst pc0 rv0.
    unfold with_rgs, mrg, L, Sp, np_front, np_rest. cbn [s_pc s_regs s_rgs s_facts s_next s_resv]. unfold front, rest. rewrite firstn_skipn. reflexivity. }
  rewrite EQ1 in Hd1.
  assert (EQb : bump (mrg L Sp) (n0 + 66) = mrg Lb Sp) by reflexivity.
  pose proof (den_bump ASEGS LIMIT model0 mem0 E _ M ms model (n0 + 66)%positive Hd1 ltac:(cbn [mrg s_next L np_front]; unfold n0; clear; lia)) as Hd2.
  rewrite EQb in Hd2.
  (* [comment removed for export] *)
  pose proof (po_inv _ _ _ _ HP0) as HI. unfold INV_A in HI. set (pz := pden E a) in *.
  pose proof (tg_pg_disj LIMIT model0 mem0 E S M ms model a mem0 Hd HP0) as Hdisj. fold pz in Hdisj.
  pose proof (az_geo pz mem0 HI) as G.
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HRG & _ & HF0 & _).
  pose proof (irange_sound E (s_facts S) SPl HF0) as Rsp. fold (uE E SPl) in Rsp.
  pose proof (irange_sound E (s_facts S) ndl HF0) as Rnd. fold (uE E ndl) in Rnd.
  set (ND := uE E ndl) in *.
  assert (HND1 : 1 <= ND <= 65536) by (clear - Rnd Cndlo Cndhi; lia).
  set (c := cls_of ND) in *.
  assert (Ec : c = tcls ND) by exact (tcls_cls_of ND HND1).
  destruct (tcls_spec ND HND1) as [Hcr HND]. rewrite <- Ec in Hcr, HND.
  assert (Hccs : In c cs).
  { apply in_crange. rewrite Ec. unfold clo, chi. split; apply tcls_mono; clear - Rnd Cndlo Cndhi HND1; lia. }
  pose proof (rng_in_cls c Hcr) as Hcin.
  destruct (cls_tbl c Hcin) as (Hszp & Hs8 & Hsz8 & Hnw & Hnm & Hmc).
  assert (Ej : uE E (p_j a c) = z_j pz c) by (symmetry; apply zn_pden).
  assert (Eca : uE E (p_ca a) = z_ca pz) by (symmetry; apply zn_pden).
  assert (Esb : uE E (p_sb a) = z_sb pz) by (symmetry; apply zn_pden).
  assert (Hjhi : z_j pz c + mc_tbl c / 2 + 1 <= 262144 / sz_tbl c).
  { rewrite forallb_forall in Cjb. pose proof (Cjb c Hccs) as X. apply Z.leb_le in X.
    pose proof (irange_sound E (s_facts S) (p_j a c) HF0) as X2. fold (uE E (p_j a c)) in X2. rewrite Ej in X2. clear - X X2. lia. }
  destruct (iz_cls _ _ HI c Hcin) as [(J0 & _)|(_ & Z1 & Jb & HIo & HPo)]; [clear - J0 Hj1; lia|].
  pose proof (iz_st _ _ HI) as HST.
  assert (Hal : uE E SPl mod 16 = 0) by (pose proof (fact_implied_ok E _ _ HF0 Cmod) as X; cbn [fact_ok] in X; exact X).
  (* [comment removed for export] *)
  destruct (rg_hdr_b_sound _ _ _ _ Cwin) as (cw & Pw). destruct (ro_b_sound _ Cro) as (zro & Hzro & Pro).
  destruct (rg_hdr_b_sound _ _ _ _ Cst) as (cst & Pst).
  assert (PS : np_shape Lb SPl (p_ca a) ndl 0 1 2).
  { constructor; cbn [Lb np_front s_pc s_resv s_regs s_rgs]; try reflexivity; try assumption.
    - exists cw. exact Pw.
    - exists zro. split; [exact Hzro | exact Pro].
    - exists (laddc (p_tg a) 2872), cst. exact Pst. }
  assert (HwLb : state_wf Lb = true) by (apply (np_front_wf_mono S (s_next S) (n0 + 66)%positive front ltac:(unfold n0; clear; lia) CwL)).
  (* [comment removed for export] *)
  unfold sb_words_ok in Csbw. destruct (rdw IMGP (s_rgs S) (lconst 923512) 8) as [l1|] eqn:W1; [|discriminate].
  destruct (rdw IMGP (s_rgs S) (lconst 923528) 8) as [l2|] eqn:W2; [|discriminate].
  apply andb_prop in Csbw as [Q1 Q2]. apply lin_eqb_eq in Q1, Q2. subst l1 l2.
  pose proof (rdw_sound IMGP IMGP_ok E _ (s_rgs S) (lconst 923512) 8 _ HRG ltac:(clear; lia) W1) as RSB.
  pose proof (rdw_sound IMGP IMGP_ok E _ (s_rgs S) (lconst 923528) 8 _ HRG ltac:(clear; lia) W2) as RRIB.
  rewrite uE_lc in RSB, RRIB by (clear; lia). rewrite Esb in RSB.
  assert (Erip : uE E (l_rip a) = z_sb pz + 137438953472).
  { unfold l_rip. rewrite uE_laddc2 by (rewrite ?Esb; unfold two64; clear - G; lia). rewrite Esb. reflexivity. }
  rewrite Erip in RRIB.
  (* [comment removed for export] *)
  assert (HCELL : forall x, 0 <= x < 2^64 -> ncell (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) x ->
            own_pt E M x /\ outside E (s_rgs (mrg Lb Sp)) (wa x) /\ ~ frz_pt E M x).
  { intros x Hx Hn. destruct (ncell_fp pz mem0 HI Hdisj c x Hcin Z1 Hn) as (F1 & F2 & F3 & F4).
    split; [exact (po_own _ _ _ _ HP0 x Hx F1)|]. split.
    - exact (pri_outside_den LIMIT model0 mem0 E (mrg L Sp) M ms model a mem0 jP jT Hd1 HP0 HjP HjT Csep x ltac:(unfold two64; clear - Hx; lia) F2 F3).
    - exact (pri_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1). }
  (* [comment removed for export] *)
  destruct (po_gp _ _ _ _ HP0) as (kp & Hgp). destruct (po_gt _ _ _ _ HP0) as (kt & Hgt).
  pose proof (band_hi LIMIT model0 mem0 E S M ms model SPl _ Hd Cband Hgp) as BP.
  pose proof (band_hi LIMIT model0 mem0 E S M ms model SPl _ Hd Cband Hgt) as BT.
  unfold gsz in BP, BT. cbn [fst snd] in BP, BT. unfold PG_SIZE, TG_SIZE in BP, BT. rewrite uE_lc in BP, BT by (clear; lia).
  assert (Epg : uE E (p_pg a) = z_pg pz) by (symmetry; apply zn_pden).
  assert (Etg : uE E (p_tg a) = z_tg pz) by (symmetry; apply zn_pden).
  rewrite Epg in BP. rewrite Etg in BT. fold (uE E SPl) in BP, BT.
  assert (ECA : uE E (p_ca a) = z_ca pz) by exact Eca.
  apply (den_npop_app cfg LIMIT model0 Hwx mem0 Lb Sp E M ms model T SPl (p_ca a) ndl 0 1 2 c (z_sb pz) (sz_tbl c) (mc_tbl c / 2) (262144 / sz_tbl c) (z_j pz c)
           Hd2 HwLb PS).
  - reflexivity.
  - exact HND1.
  - clear - Rsp Csplo Csphi. lia.
  - exact Hal.
  - rewrite ECA. exact HIo.
  - rewrite ECA. exact HST.
  - clear - Hjhi. lia.
  - exact RSB.
  - exact RRIB.
  - rewrite ECA. exact HCELL.
  - rewrite ECA. pose proof (iz_ca _ _ HI) as (X1 & X2 & X3). fold pz in X1, X2, X3. split; [exact X1|]. split; [exact X2|]. clear - G BT. lia.
  - pose proof (proj2 (iz_sb _ _ HI)) as X2. clear - G BP X2. split; [lia|]. split; [exact X2 | lia].
  - rewrite ECA. clear - G Hdisj. unfold PG_SIZE in Hdisj. lia.
  - intros E' ms' model' HD' Ha' Hfz' HI3 HST3 HR10 Hfr3.
    rewrite ECA in HI3, HST3, Hfr3.
    set (Lh := hand_post Lb 278280 KALLk [0%nat; 2%nat]) in *.
    set (VGC := (n0 + 99)%positive) in *. set (vj0 := (VGC + 1)%positive) in *.
    set (nfin := (vj0 + Pos.of_nat (2 * List.length cs))%positive) in *.
    set (chl := lscale 8 (lvar VGC)) in *.
    destruct (cls_jb pz mem0 HI c Hcin) as (K0 & K1 & K2 & _).
    assert (Hjn : z_j pz c + 1 <= 262144 / sz_tbl c) by (clear - Hjhi Hmc; lia).
    set (CHB := z_sb pz + 4294967296 * c + sz_tbl c * z_j pz c) in *.
    set (CHS := z_sh pz + 536870912 * c + sz_tbl c / 8 * z_j pz c) in *.
    assert (T1 : z_ca pz + 2592 <= z_pg pz \/ z_pg pz + 137439023104 <= z_ca pz - 128) by (clear - Hdisj G; unfold PG_SIZE in Hdisj; lia).
    assert (S1 : 2199291686912 + 2147450880 <= z_sh pz /\ z_sh pz + 17179869184 <= z_pg pz) by (clear - G; lia).
    assert (S2 : z_ca pz + 2592 <= z_sh pz \/ z_sh pz + 17179869184 <= z_ca pz - 128) by (clear - G S1; lia).
    assert (E8 : 8 * (CHS - SH_OFF) = CHB).
    { unfold CHS, CHB, SH_OFF. destruct G as (_ & _ & _ & _ & _ & Gm8 & Gsh & _).
      pose proof (Z.div_mod (z_sb pz) 8 ltac:(clear; lia)) as Ed. rewrite Gm8, Z.add_0_r in Ed. rewrite Gsh. clear - Ed Hs8. lia. }
    assert (HCHB : 0 <= CHB /\ CHB + sz_tbl c <= 2^47 /\ CHB mod 8 = 0).
    { split; [unfold CHB; clear - G Hcr K0 Hszp; nia|]. split; [unfold CHB; clear - G Hcr K0 K1 Hszp Hjn Hnm; nia|].
      rewrite <- E8. rewrite Z.mul_comm. apply Z_mod_mult. }
    (* [comment removed for export] *)
    set (TT := pz_step pz c).
    set (E'' := ext_cls (upd E' VGC (wa (CHB / 8))) vj0 cs (fT TT)).
    assert (Hs_h : s_next (mrg Lh Sp) = VGC) by (cbn [mrg Lh hand_post Lb np_front s_next]; unfold VGC; clear; lia).
    assert (Hag : agree VGC E' E'').
    { intros x Hx. unfold E''. rewrite ext_cls_lt by (unfold vj0; clear - Hx; lia). unfold upd.
      replace (Pos.eqb x VGC) with false by (symmetry; apply Pos.eqb_neq; clear - Hx; lia). reflexivity. }
    assert (Evgc : E'' VGC = wa (CHB / 8)).
    { unfold E''. rewrite ext_cls_lt by (unfold vj0; clear; lia). unfold upd. rewrite Pos.eqb_refl. reflexivity. }
    assert (Hcvo : cvals_ok E'' vj0 cs (fT TT)) by (unfold E''; apply ext_cls_ok).
    assert (Ha'' : agree (s_next Lb) E E'').
    { apply (agree_trans _ E E' E''); [exact Ha'|]. apply (agree_mono _ VGC); [cbn [Lb np_front s_next]; unfold VGC; clear; lia | exact Hag]. }
    pose proof (den_agree ASEGS LIMIT model0 (ms_mem ms') E' E'' _ M ms' model' HD' ltac:(rewrite Hs_h; exact Hag)) as HD''.
    assert (Hfz'' : forall w, frz_pt E M w -> ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) by exact Hfz'.
    clear HD'.
    set (hyb := hyb_p (ncell_b (z_ca pz) (z_sb pz) c (262144 / sz_tbl c)) (ms_mem ms') mem0).
    assert (HwfM : sm_wf (s_next Lb) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd2).
    assert (HbwS : bases_wf (s_next Lb) (s_rgs (mrg Lb Sp)) = true) by exact (dn_bases _ _ _ _ _ _ _ _ _ Hd2).
    assert (Hsh : shape (s_rgs (mrg Lh Sp)) = shape (s_rgs (mrg Lb Sp))).
    { cbn [mrg s_rgs]. unfold Lh, hand_post. cbn [s_rgs]. unfold shape. rewrite !map_app. f_equal.
      pose proof (empty_at_shape [0%nat; 2%nat] (s_rgs Lb) 0) as Hs. unfold shape in Hs. exact Hs. }
    pose proof (dn_own _ _ _ _ _ _ _ _ _ Hd2) as Hown2.
    (* [comment removed for export] *)
    assert (Hnwin : forall w, outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w) -> 0 <= w < two64 -> ~ (uE E SPl - 2048 <= w < uE E SPl)).
    { intros w Hout Hw Hc0. unfold outside in Hout. rewrite Forall_forall in Hout. cbn [mrg s_rgs] in Hout.
      specialize (Hout _ ltac:(apply in_or_app; left; exact (nth_error_In _ _ Pw))). cbn [rg_base] in Hout.
      unfold rsz in Hout. cbn [rg_size] in Hout. rewrite lden_lconst, (u_small64 2048) in Hout by (unfold two64; clear; lia).
      rewrite lden_laddc in Hout. fold (uE E SPl) in Hout. rewrite (u_small64 (uE E SPl + -2048)) in Hout by (clear - Rsp Csplo Csphi; unfold two64; lia).
      rewrite u_small64 in Hout by exact Hw. clear - Hout Hc0. lia. }
    (* [comment removed for export] *)
    assert (Hkeep0 : forall w, 0 <= w < two64 -> own_pt E M w -> outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w) ->
              ~ owned_C (z_ca pz) (z_sb pz) c w -> ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
    { intros w Hw (q & Hq & Hqw) Hout Hnc. destruct (Hown2 q Hq w Hqw) as [Hv Hm]. rewrite <- (Hm Hout).
      apply Hfr3; [unfold two64 in Hw; clear - Hw; lia | exact Hv | exact (Hnwin w Hout Hw) | exact Hnc]. }
    assert (Hkeep : forall w, 0 <= w < two64 -> own_pt E M w -> outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w) ->
              ~ ncell (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) w -> ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
    { intros w Hw Hq Hout Hnc. apply (Hkeep0 w Hw Hq Hout).
      intros Hoc. apply Hnc. unfold owned_C in Hoc. unfold ncell, foot_Co. clear - Hoc. lia. }
    assert (Hfrzn : forall w, frz_pt E M w -> hyb (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
    { intros w Hw. unfold hyb, hyb_p. destruct (ncell_b _ _ _ _ _); [exact (Hfz' w Hw) | reflexivity]. }
    assert (Hw64 : forall w, own_pt E M w -> 0 <= w < two64).
    { intros w Hw0. destruct (Z_lt_le_dec w two64) as [X|X].
      - destruct Hw0 as (q & Hq & Hqw). pose proof (uE_range E (fst q)) as Uq. clear - Uq Hqw X. lia.
      - exfalso. destruct (ha_ownx _ _ _ _ HA0 w (own_pt_a_M E M a w Hown_eq Hw0)) as [Dc|[_ Pf]].
        + destruct HA0 as [(n1 & F0 & st0 & I0 & _) _ _ _ _ _ _]. destruct I0 as [_ _ _ D1r _ _ _ _ _ B1r _ _ _].
          unfold dcov in Dc. unfold two64 in X. clear - Dc X D1r B1r. lia.
        + pose proof (pri_foot_rng E a mem0 HI w Pf) as Pr. unfold two64 in X. clear - Pr X. lia. }
    assert (HD3 : DEN ASEGS LIMIT model0 hyb E'' (mrg Lh Sp) M ms' model').
    { apply (den_snap ASEGS LIMIT model0 (ms_mem ms') hyb E'' _ M ms' model' HD'').
      - intros w Hw. pose proof (proj1 (frz_pt_agree (s_next Lb) E E'' M w HwfM Ha'') Hw) as Hw0.
        rewrite (Hfrzn w Hw0). symmetry. exact (Hfz' w Hw0).
      - intros w Hw Hout. unfold hyb, hyb_p.
        destruct (ncell_b (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) (bv_unsigned (Z_to_bv 64 w))) eqn:Eb; [reflexivity|].
        assert (Hw0 : own_pt E M w) by exact (proj1 (own_pt_agree (s_next Lb) E E'' M w HwfM Ha'') Hw).
        assert (Hout0 : outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w)) by exact (outside_agree_shape _ E E'' _ _ _ HbwS Ha'' Hsh Hout).
        pose proof (Hw64 w Hw0) as Hw6.
        rewrite u_small64 in Eb by exact Hw6. symmetry. apply (Hkeep w Hw6 Hw0 Hout0).
        intros Hn. apply ncell_b_spec in Hn. congruence. }
    (* [comment removed for export] *)
    set (X0 := mrg Lh Sp) in *.
    pose proof (den_uncarve ASEGS LIMIT model0 hyb E'' X0 M ms' model' _ _ l'' HD3 CpX Hsteps) as HD5.
    (* [comment removed for export] *)
    assert (HawLb : awf (s_next Lb) a = true) by (apply (awf_mono (s_next S)); [cbn [Lb np_front s_next]; unfold n0; clear; lia | exact Haw]).
    pose proof (HA_on_agree (s_next Lb) E E'' M a mem0 HA0 HwfM HawLb Ha'') as HA0'.
    assert (Epz' : pden E'' a = pz) by exact (pden_agree (s_next Lb) E E'' a HawLb Ha'').
    pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ HD3)) as (_ & _ & _ & _ & _ & _ & HF4 & _).
    assert (Hnewpt : forall x, pri_foot_z pz x -> FPmax pz x -> ~ alloc_part pz x -> 0 <= x < 2^47 ->
              ~ ncell (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) x ->
              own_pt E'' M x /\ outside E'' l'' (Z_to_bv 64 x) /\ ms_mem ms' (Z_to_bv 64 x) = mem0 (Z_to_bv 64 x)).
    { intros x F1 F2 F3 F4 F5. assert (Hx64 : 0 <= x < two64) by (unfold two64; clear - F4; lia).
      assert (Hox : own_pt E M x) by (apply (po_own _ _ _ _ HP0 x); [clear - F4; lia | exact F1]).
      pose proof (pri_outside_den LIMIT model0 mem0 E (mrg L Sp) M ms model a mem0 jP jT Hd1 HP0 HjP HjT Csep x Hx64 F2 F3) as Hout.
      split; [exact (proj2 (own_pt_agree (s_next Lb) E E'' M x HwfM Ha'') Hox)|]. split.
      - apply (uncarve_outside E'' X0 _ 2 stk l'' _ HF4 CpX Hsteps).
        apply (outside_shape E'' (s_rgs (mrg Lb Sp))); [exact Hsh|]. exact (proj1 (outside_agree (s_next Lb) E E'' _ _ HbwS Ha'') Hout).
      - exact (Hkeep x Hx64 Hox Hout F5). }
    (* [comment removed for export] *)
    assert (Hcpt : forall x, CHB <= x < CHB + sz_tbl c ->
              own_pt E'' M x /\ outside E'' l'' (Z_to_bv 64 x) /\ ms_mem ms' (Z_to_bv 64 x) = Some (Z_to_bv 8 0) /\ app_pt model' x /\ x < alloc_top (m_vmmaps model')).
    { intros x Hx. destruct (chunk_fp pz mem0 HI c x Hcin Z1 Hjn Hx) as (F1 & F2 & F3 & F4 & F5).
      assert (F6 : ~ ncell (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) x).
      { unfold ncell, foot_Co. unfold CHB in Hx. clear - Hx F5 T1 G Hcr K0 Hszp. lia. }
      destruct (Hnewpt x F1 F2 F3 F4 F6) as (N1 & N2 & N3).
      assert (Hns : in_shadow x = false).
      { unfold in_shadow, SH_LO, SH_HI. apply andb_false_iff. right. apply Z.ltb_ge. unfold CHB in Hx. clear - Hx G Hcr K0 Hszp. lia. }
      assert (Hcov : covered (vm_maps (m_vmmaps model')) x = true).
      { apply (pri_covered LIMIT model0 hyb E'' _ M ms' model' a mem0 HD3 HA0' Hne x); [unfold pri_foot; rewrite Epz'; exact F1 | exact Hns |].
        unfold CHB in Hx. clear - Hx G Hcr K0 Hszp. lia. }
      split; [exact N1|]. split; [exact N2|]. split.
      - rewrite N3. destruct HPo as [Pm _ _]. apply Pm. unfold RBX. unfold CHB in Hx. clear - Hx F5. lia.
      - split; [|exact (covered_below_top ASEGS LIMIT model0 hyb E'' _ M ms' model' x HD3 Hcov)].
        split; [left; unfold covered in *; rewrite existsb_app; rewrite Hcov; apply orb_true_r|]. split; [exact Hns | exact F4]. }
    (* [comment removed for export] *)
    assert (Hspt : forall x, CHS <= x < CHS + sz_tbl c / 8 ->
              own_pt E'' M x /\ outside E'' l'' (Z_to_bv 64 x) /\ ms_mem ms' (Z_to_bv 64 x) = Some (Z_to_bv 8 250) /\
              in_shadow x = true /\ covered (vm_maps (m_vmmaps model')) x = true /\ 0 <= x < 2^47).
    { intros x Hx. destruct (chsh_fp pz mem0 HI c x Hcin Hjn Hx) as (F1 & F2 & F3 & F4 & F5).
      assert (F6 : ~ ncell (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) x).
      { unfold ncell, foot_Co. unfold CHS in Hx. clear - Hx F5 S1 S2 G Hcr K0 Hsz8. lia. }
      destruct (Hnewpt x F1 F2 F3 F4 F6) as (N1 & N2 & N3).
      assert (Hzr : in_zr (sm_zr M) x = true).
      { apply (po_zr _ _ _ _ HP0). exists c. split; [exact Hcin|]. left. fold pz. unfold CHS in Hx. clear - Hx F5 K0 Hsz8. split; [|exact F5].
        assert (0 <= sz_tbl c / 8 * z_j pz c) by (apply Z.mul_nonneg_nonneg; lia). lia. }
      split; [exact N1|]. split; [exact N2|]. split.
      - rewrite N3. destruct HPo as [_ Ps _]. apply Ps. unfold SHX. unfold CHS in Hx. clear - Hx F5. lia.
      - split; [exact (dn_zrsh _ _ _ _ _ _ _ _ _ HD3 x Hzr)|]. split; [exact (dn_zrm _ _ _ _ _ _ _ _ _ HD3 x Hzr) | exact F4]. }
    (* [comment removed for export] *)
    assert (Hwnd : lwf (s_next S) ndl = true).
    { pose proof (dn_sden _ _ _ _ _ _ _ _ _ Hd) as XS. pose proof CwL as XW. unfold state_wf in XW. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _].
      exact (regs_wf_n_spec _ _ 31 XW 12%nat ltac:(clear; lia)). }
    assert (End'' : uE E'' ndl = ND).
    { apply (uE_agree (s_next Lb) E E''); [apply (lwf_mono' (s_next S)); [cbn [Lb np_front s_next]; unfold n0; clear; lia | exact Hwnd] | exact Ha'']. }
    assert (Hwnd8 : lwf (s_next S) ND8 = true) by exact (ldiv8_wf _ _ _ Hnd8 Hwnd).
    assert (End8 : uE E'' ND8 = uE E ND8).
    { apply (uE_agree (s_next Lb) E E''); [apply (lwf_mono' (s_next S)); [cbn [Lb np_front s_next]; unfold n0; clear; lia | exact Hwnd8] | exact Ha'']. }
    pose proof (irange_sound E (s_facts S) ND8 HF0) as Rnd8. fold (uE E ND8) in Rnd8.
    assert (End8b : ND = 8 * uE E ND8) by (apply (uE_ldiv8 E ndl ND8 Hnd8); unfold two64; clear - Rnd8 Cnd8; lia).
    set (N8 := uE E ND8) in *.
    assert (HN8 : 1 <= N8 /\ 8 * N8 <= sz_tbl c) by (clear - End8b HND1 HND; lia).
    (* [comment removed for export] *)
    set (Y0 := with_rgs X0 l'') in *.
    assert (Hny : s_next Y0 = VGC) by exact Hs_h.
    assert (Hnf : (VGC < nfin)%positive) by (unfold nfin, vj0; clear; lia).
    pose proof (den_bump ASEGS LIMIT model0 hyb E'' Y0 M ms' model' nfin HD5 ltac:(rewrite Hny; clear - Hnf; lia)) as HD6.
    assert (Echl : forall E3, agree nfin E'' E3 -> lden E3 chl = wa CHB).
    { intros E3 Ha3. unfold chl. rewrite lden_lscale, lden_lvar. rewrite <- (Ha3 VGC Hnf), Evgc.
      rewrite u_wa_small by (destruct HCHB as (B1 & B2 & _); split; [apply Z.div_pos; [exact B1 | clear; lia] | apply Z.div_lt_upper_bound; [clear; lia | clear - B1 B2 Hszp; lia]]).
      unfold wa. f_equal. destruct HCHB as (_ & _ & B3). pose proof (Z.div_mod CHB 8 ltac:(clear; lia)) as Ed. rewrite B3, Z.add_0_r in Ed. symmetry. exact Ed. }
    assert (Hch : forall E3, agree (s_next (bump Y0 nfin)) E'' E3 -> lden E3 chl = lden E3 (rget (s_regs (bump Y0 nfin)) (rk 10))).
    { intros E3 Ha3. rewrite (Echl E3 Ha3). pose proof (dn_sden _ _ _ _ _ _ _ _ _ HD6 E3 Ha3) as (_ & _ & _ & Hregs & _).
      specialize (Hregs (Z_to_bv 5 10)). cbn [restrict ms_regs] in Hregs. change (rkey (Z_to_bv 5 10)) with (rk 10) in Hregs.
      rewrite <- Hregs, HR10. unfold CHB, wa. f_equal. ring. }
    assert (Hrk : rk 10 <> xH) by (intros Hc0; vm_compute in Hc0; discriminate).
    pose proof (den_reg_eq ASEGS LIMIT model0 hyb E'' _ M ms' model' (rk 10) chl HD6 Hrk Hch) as HD7.
    set (Y1 := with_reg (bump Y0 nfin) (rk 10) chl) in *.
    (* [comment removed for export] *)
    pose proof (iz_len _ _ HI) as Hlenz.
    assert (Hcsr : forall c', In c' cs -> 1 <= c' <= 30).
    { intros c' Hc'. apply crange_rng in Hc'. clear - Hc' Cclo1 Cchi. lia. }
    assert (HTT : forall k, 0 <= nth k TT 0 < 2^64).
    { unfold TT, pz. apply pz_step_nth_rng; [exact Hlen | exact Hcr | fold pz; clear - K0 Hjn Hnw; lia]. }
    assert (Hwsb : lwf (s_next S) (p_sb a) = true) by (apply lwf_p_nth; exact (awf_pri _ a Haw)).
    pose proof (irange_sound E (s_facts S) (p_sb a) HF0) as Rsb. fold (uE E (p_sb a)) in Rsb. rewrite Esb in Rsb.
    assert (Hsz32 : sz_tbl c mod 32 = 0) by exact (sz_tbl_mod32 c Hcr).
    assert (Hclc : clo <= c <= chi) by (apply crange_rng; exact Hccs).
    set (newfacts := FRange (lvar VGC) ((fst (irange (s_facts S) (p_sb a)) + 4294967296 * clo) / 8) ((snd (irange (s_facts S) (p_sb a)) + 4294967296 * chi + 262144) / 8) ::
                     FMod (lvar VGC) 2 0 :: FRange (lsub chl (p_sb a)) (4294967296 * clo) (4294967296 * chi + 262144) :: class_facts (s_facts S) a vj0 cs).
    assert (Hnfacts : forall E3, agree (s_next Y1) E'' E3 -> Forall (fact_ok E3) newfacts).
    { intros E3 Ha3. change (s_next Y1) with nfin in Ha3.
      assert (Ev3 : bv_unsigned (lden E3 (lvar VGC)) = CHB / 8).
      { rewrite lden_lvar, <- (Ha3 VGC Hnf), Evgc. apply u_wa_small. destruct HCHB as (B1 & B2 & _).
        split; [apply Z.div_pos; [exact B1 | clear; lia] | apply Z.div_lt_upper_bound; [clear; lia | clear - B1 B2 Hszp; lia]]. }
      assert (Hsj : 0 <= sz_tbl c * z_j pz c /\ sz_tbl c * z_j pz c + 32 <= 262144) by (clear - K0 Hszp Hjn Hnm; nia).
      unfold newfacts. constructor; [|constructor; [|constructor]].
      - cbn [fact_ok]. rewrite Ev3. split; apply Z.div_le_mono; try (clear; lia); unfold CHB; clear - Rsb Hclc Hsj; clearbody c clo chi pz;
          destruct Rsb as [R1 R2]; destruct Hclc as [C1 C2]; destruct Hsj as [J1 J2]; revert R1 R2 C1 C2 J1 J2;
          generalize (sz_tbl c * z_j pz c) (z_sb pz) (fst (irange (s_facts S) (p_sb a))) (snd (irange (s_facts S) (p_sb a))); clear; intros; lia.
      - cbn [fact_ok]. rewrite Ev3. destruct HCHB as (_ & _ & B3).
        assert (H32 : CHB mod 32 = 0).
        { unfold CHB. pose proof (iz_sb _ _ HI) as (_ & X2). fold pz in X2.
          rewrite Z.add_mod by (clear; lia). rewrite (Z.add_mod (z_sb pz)) by (clear; lia).
          replace (z_sb pz mod 32) with 0 by (symmetry; pose proof (Z.div_mod (z_sb pz) 4096 ltac:(clear; lia)) as Ed; rewrite X2, Z.add_0_r in Ed; rewrite Ed;
            replace (4096 * (z_sb pz / 4096)) with (128 * (z_sb pz / 4096) * 32) by ring; apply Z_mod_mult).
          replace ((4294967296 * c) mod 32) with 0 by (symmetry; replace (4294967296 * c) with (134217728 * c * 32) by ring; apply Z_mod_mult).
          replace ((sz_tbl c * z_j pz c) mod 32) with 0 by (symmetry; rewrite Z.mul_mod by (clear; lia); rewrite Hsz32; reflexivity).
          reflexivity. }
        pose proof (Z.div_mod CHB 32 ltac:(clear; lia)) as Ed. rewrite H32, Z.add_0_r in Ed. rewrite Ed.
        replace (32 * (CHB / 32)) with (CHB / 32 * 4 * 8) by ring. rewrite Z.div_mul by (clear; lia). change (2 ^ 2) with 4. apply Z_mod_mult.
      - cbn [fact_ok]. rewrite lden_lsub, (Echl E3 Ha3).
        assert (Esb3 : lden E3 (p_sb a) = wa (z_sb pz)).
        { rewrite (lden_agree_wf (s_next S) E E3 _ Hwsb); [unfold wa; rewrite <- Esb; unfold uE; rewrite Z_to_bv_bv_unsigned; reflexivity|].
          apply (agree_trans _ E E'' E3); [apply (agree_mono _ (s_next Lb)); [cbn [Lb np_front s_next]; unfold n0; clear; lia | exact Ha''] |
            apply (agree_mono _ nfin); [cbn [Lb np_front s_next]; unfold nfin, vj0, VGC, n0; clear; lia | exact Ha3]]. }
        rewrite Esb3. rewrite bv_sub_unsigned. unfold wa. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
        destruct HCHB as (B1 & B2 & _).
        rewrite (Z.mod_small CHB) by (unfold two64; clear - B1 B2 Hszp; lia). rewrite (Z.mod_small (z_sb pz)) by (unfold two64; clear - G; lia).
        rewrite Z.mod_small by (unfold CHB, two64; clear - Hsj Hcr; lia). unfold CHB. clear - Hsj Hclc. lia.
      - apply (class_facts_ok cs E3 (s_facts S) a vj0 TT); [| exact HTT |].
        + apply (cvals_ok_agree cs E'' E3 vj0 (fT TT) nfin Hcvo Ha3). unfold nfin. clear. lia.
        + intros c' Hc'. pose proof (Hcsr c' Hc') as Hcr'. pose proof (cidx_rng c' Hcr') as Hi'.
          pose proof (irange_sound E (s_facts S) (p_j a c') HF0) as Rj'. fold (uE E (p_j a c')) in Rj'.
          assert (Ej' : uE E (p_j a c') = z_j pz c') by (symmetry; apply zn_pden). rewrite Ej' in Rj'.
          change (nth (5 + 2 * cidx c') TT 0) with (z_j TT c'). change (nth (6 + 2 * cidx c') TT 0) with (z_z TT c'). unfold TT.
          (* [comment removed for export] *)
          assert (Ej3 : uE E3 (p_j a c') = z_j pz c').
          { rewrite <- Ej'. apply (uE_agree (s_next S) E E3); [apply lwf_p_nth; exact (awf_pri _ a Haw)|].
            apply (agree_trans _ E E'' E3); [apply (agree_mono _ (s_next Lb)); [cbn [Lb np_front s_next]; unfold n0; clear; lia | exact Ha''] |
              apply (agree_mono _ nfin); [cbn [Lb np_front s_next]; unfold nfin, vj0, VGC, n0; clear; lia | exact Ha3]]. }
          rewrite Ej3.
          destruct (Z.eq_dec c' c) as [->|Hne'].
          * rewrite (step_j_same pz c Hlenz Hcr), (step_z_same pz c Hlenz Hcr). clear - Rj'. lia.
          * rewrite (step_j_other pz c Hlenz Hcr c' Hcr' Hne'), (step_z_other pz c Hlenz Hcr c' Hcr' Hne').
            destruct (cls_jb pz mem0 HI c' (rng_in_cls c' Hcr')) as (_ & _ & _ & Kz). clear - Rj' Kz. lia. }
    pose proof (den_add_facts ASEGS LIMIT model0 hyb E'' Y1 M ms' model' newfacts HD7 Hnfacts) as HD8.
    set (Y2 := with_facts Y1 (s_facts Y1 ++ newfacts)) in *.
    (* [comment removed for export] *)
    set (R2 := RG (laddc (lvar VGC) SH_OFF) ND8 RW (tset 1%positive (BK 250) TEmpty)).
    set (R1 := RG chl ndl RZ TEmpty).
    assert (Hny2 : s_next Y2 = nfin) by reflexivity.
    assert (Hrgs2 : s_rgs Y2 = l'') by reflexivity.
    assert (Ech'' : uE E'' chl = CHB).
    { unfold uE. rewrite (Echl E'' (fun x _ => eq_refl)). apply u_wa_small. destruct HCHB as (B1 & B2 & _). clear - B1 B2 Hszp. lia. }
    assert (Ecs'' : uE E'' (laddc (lvar VGC) SH_OFF) = CHS).
    { assert (Ev : uE E'' (lvar VGC) = CHB / 8).
      { apply uE_lvar_wa; [exact Evgc|]. destruct HCHB as (B1 & B2 & _).
        split; [apply Z.div_pos; [exact B1 | clear; lia] | apply Z.div_lt_upper_bound; [clear; lia | clear - B1 B2 Hszp; lia]]. }
      assert (Ed : CHB / 8 = CHS - SH_OFF) by (rewrite <- E8; rewrite Z.mul_comm; apply Z.div_mul; clear; lia).
      rewrite uE_laddc_z by (rewrite Ev, Ed; unfold two64, CHS; clear - G S1 K0 K2 Hcr Hsz8; lia). rewrite Ev, Ed. ring. }
    assert (Er2 : rsz E'' R2 = N8) by (unfold rsz, R2; cbn [rg_size]; fold (uE E'' ND8); exact End8).
    assert (Er1 : rsz E'' R1 = ND) by (unfold rsz, R1; cbn [rg_size]; fold (uE E'' ndl); exact End'').
    assert (Hwn : forall l, lwf (s_next S) l = true -> lwf nfin l = true).
    { intros l Hl. apply (lwf_mono' (s_next S)); [unfold nfin, vj0, VGC, n0; clear; lia | exact Hl]. }
    assert (HD9 : DEN ASEGS LIMIT model0 hyb E'' (addo_post Y2 R2) M ms' model').
    { apply (den_add_own ASEGS LIMIT model0 hyb E'' Y2 M ms' model' R2 HD8).
      - rewrite Hny2. apply lwf_laddc. apply lwf_lvar. exact Hnf.
      - rewrite Hny2. exact (Hwn _ Hwnd8).
      - reflexivity.
      - intros p v Hp. unfold R2 in Hp. cbn [rg_cont] in Hp. destruct (Pos.eq_dec 1 p) as [<-|Hnp].
        + rewrite tget_tset_same in Hp. injection Hp as <-. exists 250. reflexivity.
        + rewrite tget_tset_other in Hp by exact Hnp. rewrite tget_empty in Hp. discriminate.
      - rewrite Er2. clear - HN8. lia.
      - rewrite Er2. change (rg_base R2) with (laddc (lvar VGC) SH_OFF). rewrite Ecs''.
        destruct (Hspt (CHS + sz_tbl c / 8 - 1) ltac:(clear - Hsz8; lia)) as (_ & _ & _ & _ & _ & N6). clear - N6 HN8 Hs8. lia.
      - intros x Hx. rewrite Er2 in Hx. change (rg_base R2) with (laddc (lvar VGC) SH_OFF) in Hx. rewrite Ecs'' in Hx.
        destruct (Hspt x ltac:(clear - Hx HN8 Hs8; lia)) as (N1 & _ & N3 & _ & N5 & _). split; [exact N1|]. split; [rewrite N3; discriminate|].
        exact (covered_below_top ASEGS LIMIT model0 hyb E'' _ M ms' model' x HD3 N5).
      - intros p b Hp. unfold R2 in Hp. cbn [rg_cont] in Hp. rewrite Er2. change (rg_base R2) with (laddc (lvar VGC) SH_OFF). rewrite Ecs''.
        destruct (Pos.eq_dec 1 p) as [<-|Hnp]; [|rewrite tget_tset_other in Hp by exact Hnp; rewrite tget_empty in Hp; discriminate].
        rewrite tget_tset_same in Hp. injection Hp as <-. split; [clear - HN8; lia|].
        destruct (Hspt (CHS + (1 - 1)) ltac:(clear - Hsz8; lia)) as (_ & _ & N3 & _). exact N3.
      - intros R' HR' w Hw Hc0. rewrite Er2 in Hc0. change (rg_base R2) with (laddc (lvar VGC) SH_OFF) in Hc0. rewrite Ecs'' in Hc0. rewrite Hrgs2 in HR'.
        destruct (Hspt w ltac:(clear - Hc0 HN8 Hs8; lia)) as (_ & N2 & _ & _ & _ & N6). unfold outside in N2. rewrite Forall_forall in N2. specialize (N2 R' HR').
        rewrite u_small64 in N2 by (clear - N6; unfold two64; lia). unfold uE in Hw. clear - N2 Hw. lia.
      - unfold rl_ok. cbv zeta. rewrite Er2. change (rg_base R2) with (laddc (lvar VGC) SH_OFF). rewrite Ecs''. split; [clear - HN8; lia|]. right.
        split; [unfold SH_OFF, CHS; clear - S1 K0 Hcr Hsz8; lia|]. split.
        + intros x Hx. apply (Hcpt x). rewrite <- E8. clear - Hx HN8 Hs8. lia.
        + intros w Hw. destruct (Hspt w ltac:(clear - Hw HN8 Hs8; lia)) as (_ & _ & _ & N4 & N5 & _). split; [exact N4 | exact N5]. }
    assert (HD10 : DEN ASEGS LIMIT model0 hyb E'' (addo_post (addo_post Y2 R2) R1) M ms' model').
    { apply (den_add_own_z ASEGS LIMIT model0 hyb E'' (addo_post Y2 R2) M ms' model' R1 HD9).
      - cbn [addo_post s_next]. rewrite Hny2. unfold R1. cbn [rg_base]. unfold chl. apply lwf_lscale. apply lwf_lvar. exact Hnf.
      - cbn [addo_post s_next]. rewrite Hny2. exact (Hwn _ Hwnd).
      - reflexivity.
      - reflexivity.
      - rewrite Er1. clear - HND1. lia.
      - rewrite Er1. change (rg_base R1) with chl. rewrite Ech''. destruct HCHB as (_ & B2 & _). clear - B2 HND. lia.
      - intros x Hx. rewrite Er1 in Hx. change (rg_base R1) with chl in Hx. rewrite Ech'' in Hx.
        destruct (Hcpt x ltac:(clear - Hx HND; lia)) as (N1 & _ & N3 & _ & N5). split; [exact N1|]. split; [exact N3 | exact N5].
      - intros R' HR' w Hw Hc0. rewrite Er1 in Hc0. change (rg_base R1) with chl in Hc0. rewrite Ech'' in Hc0.
        cbn [addo_post s_rgs] in HR'. destruct HR' as [<-|HR'].
        + rewrite Er2 in Hw. change (rg_base R2) with (laddc (lvar VGC) SH_OFF) in Hw. rewrite Ecs'' in Hw.
          destruct (Hspt w ltac:(clear - Hw HN8 Hs8; lia)) as (_ & _ & _ & N4 & _). destruct (Hcpt w ltac:(clear - Hc0 HND; lia)) as (_ & _ & _ & Happ & _).
          unfold app_pt in Happ. destruct Happ as (_ & N4' & _). congruence.
        + rewrite Hrgs2 in HR'. destruct (Hcpt w ltac:(clear - Hc0 HND; lia)) as (_ & N2 & _ & Happ & _). unfold app_pt in Happ. destruct Happ as (_ & _ & N6).
          unfold outside in N2. rewrite Forall_forall in N2. specialize (N2 R' HR').
          rewrite u_small64 in N2 by (clear - N6; unfold two64; lia). unfold uE in Hw. clear - N2 Hw. lia.
      - unfold rl_ok. cbv zeta. rewrite Er1. change (rg_base R1) with chl. rewrite Ech''. split; [clear - HND1; lia|]. left.
        intros w Hw. destruct (Hcpt w ltac:(clear - Hw HND; lia)) as (_ & _ & _ & N4 & _). exact N4. }
    (* [comment removed for export] *)
    assert (Hhyb_in : forall x, 0 <= x < 2^64 -> ncell (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) x -> hyb (wa x) = ms_mem ms' (wa x)).
    { intros x Hx Hn. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx. rewrite (proj2 (ncell_b_spec _ _ _ _ _) Hn). reflexivity. }
    assert (Hhyb_out : forall x, 0 <= x < 2^64 -> ~ ncell (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) x -> hyb (wa x) = mem0 (wa x)).
    { intros x Hx Hn. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx.
      destruct (ncell_b (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) x) eqn:Eb; [exfalso; apply Hn; apply ncell_b_spec; exact Eb | reflexivity]. }
    assert (B0 : 0 <= z_ca pz /\ z_ca pz + 4096 <= 2^63 /\ 0 <= z_sb pz /\ z_sb pz + 137438953472 + 4096 <= 2^63) by (clear - G; lia).
    assert (HIo' : INV_Co hyb (z_ca pz) (z_sb pz) c (sz_tbl c) (mc_tbl c / 2) (262144 / sz_tbl c) (z_j pz c + 1)).
    { apply (INV_Co_frame (ms_mem ms')); [clear - B0; lia | clear - B0; lia | clear - B0; lia | clear - B0; lia | | exact (INV_G_o _ _ _ _ _ _ _ _ HI3)].
      intros x Hf. apply Hhyb_in; [unfold foot_Co in Hf; clear - Hf B0 Hcr Hnw; lia | left; exact Hf]. }
    assert (HST' : STATS hyb (z_ca pz)).
    { apply (STATS_frame (ms_mem ms')); [clear - B0; lia | clear - B0; lia | | exact HST3].
      intros x Hx. apply Hhyb_in; [clear - Hx B0; lia | right; exact Hx]. }
    assert (HPo' : POP_C hyb (z_sb pz) (z_sh pz) c (sz_tbl c) (z_j pz c + 1)).
    { assert (Hsz0 : 0 <= sz_tbl c) by (clear - Hszp; lia).
      apply (POP_C_frame mem0); [| clear - K0 Hsz8; nia | exact (POP_C_step mem0 (z_sb pz) (z_sh pz) c (sz_tbl c) (z_j pz c) Hsz0 K0 HPo)].
      intros x Hx. unfold RBX, SHX in Hx. apply Hhyb_out.
      - destruct Hx as [Hx|Hx]; [clear - Hx B0 Hcr K0 Hszp; nia | clear - Hx S1 G Hcr K0 Hsz8; nia].
      - unfold ncell, foot_Co. destruct Hx as [Hx|Hx].
        + assert (0 <= sz_tbl c * (z_j pz c + 1)) by (clear - K0 Hszp; nia). clear - Hx H T1 G Hcr. lia.
        + assert (0 <= sz_tbl c / 8 * (z_j pz c + 1)) by (clear - K0 Hsz8; nia). clear - Hx H S1 S2 G Hcr. lia. }
    assert (HIz' : INV_Az TT hyb).
    { apply (INV_Az_step pz mem0 hyb c HI Hdisj Hcin ltac:(clear - Hjhi; lia) HIo' HPo' HST').
      intros x Hf Hno. pose proof (pri_foot_rng E a mem0 HI x Hf) as Pr. assert (Hx : 0 <= x < 2^64) by (clear - Pr; lia).
      destruct (ncell_b (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) x) eqn:Eb.
      - apply ncell_b_spec in Eb. rewrite (Hhyb_in x Hx Eb). destruct (HCELL x Hx Eb) as (Q1 & Q2 & _).
        apply (Hkeep0 x ltac:(unfold two64; clear - Hx; lia) Q1 Q2 Hno).
      - apply (Hhyb_out x Hx). intros Hn. apply ncell_b_spec in Hn. congruence. }
    (* [comment removed for export] *)
    set (pri' := set_classes vj0 cs (a_pri a)) in *.
    set (aw := a_with a pri').
    assert (Epz2 : pden E'' aw = TT).
    { unfold pden. change (a_pri aw) with pri'. unfold pri'. rewrite (map_set_classes cs E'' vj0 (a_pri a) TT Hcvo HTT).
      fold (pden E'' a). rewrite Epz'. exact (setz_step cs pz c Hlenz Hcsr Hccs). }
    assert (Hne' : pri' <> []).
    { intros Hn. pose proof (f_equal (@List.length lin) Hn) as XL. unfold pri' in XL. rewrite set_classes_length, Hlen in XL. discriminate. }
    assert (Hbase : forall k, (k < 5)%nat -> nth k pri' lc0 = nth k (a_pri a) lc0).
    { intros k Hk5. unfold pri'. exact (set_classes_base cs vj0 (a_pri a) k Hk5 Hcsr Hlen). }
    assert (Hmono : forall x, pri_foot_z (pden E a) x -> pri_foot_z (pden E'' (a_with a pri')) x).
    { intros x Hf. change (a_with a pri') with aw. rewrite Epz2. fold pz in Hf. unfold TT, pri_foot_z in *.
      rewrite (step_ca pz c Hlenz Hcr), (step_sb pz c Hlenz Hcr), (step_sh pz c Hlenz Hcr).
      destruct Hf as [Hf|[Hf|[Hf|(c' & Hc' & Hf)]]]; [left; exact Hf | right; left; exact Hf | right; right; left; exact Hf |]. right. right. right. exists c'. split; [exact Hc'|].
      destruct (Z.eq_dec c' c) as [->|Hnc]; [rewrite (step_z_same pz c Hlenz Hcr); rewrite Z1 in Hf; exact Hf|].
      rewrite (step_z_other pz c Hlenz Hcr c' (in_cls_rng c' Hc') Hnc). exact Hf. }
    assert (Hdepf : forall x, 0 <= x < 2^64 -> downed (dD1 E a) (dB1 E a) x -> hyb (wa x) = mem0 (wa x)).
    { intros x Hx Hdw. apply (Hhyb_out x Hx). intros Hn. destruct (ncell_fp pz mem0 HI Hdisj c x Hcin Z1 Hn) as (F1 & _).
      exact (pri_not_downed LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1 Hdw). }
    assert (Hjmono : forall c', In c' CLS -> z_j pz c' <= z_j TT c').
    { intros c' Hc'. unfold TT. destruct (Z.eq_dec c' c) as [->|Hnc]; [rewrite (step_j_same pz c Hlenz Hcr); clear; lia|].
      rewrite (step_j_other pz c Hlenz Hcr c' (in_cls_rng c' Hc') Hnc). clear. lia. }
    assert (Hext_step : forall b z, ext_sem (pden E a) b z -> ext_sem (pden E'' (a_with a pri')) b z).
    { intros b z Hbz. change (a_with a pri') with aw. rewrite Epz2. apply (ext_sem_mono pz); [| exact Hjmono | | | | | exact Hbz]; unfold TT.
      - exact (step_sb pz c Hlenz Hcr). - exact (step_qn pz c Hlenz Hcr). - exact (step_qj pz c Hlenz Hcr).
      - exact (step_gn pz c Hlenz Hcr). - exact (step_gl pz c Hlenz Hcr). }
    (* [comment removed for export] *)
    assert (Hext_fr : forall b z, ext_sem (pden E a) b z -> forall x, b <= x < b + z -> hyb (wa x) = mem0 (wa x)).
    { intros b z Hbz x Hxr. destruct (ext_sem_pt pz mem0 HI b z x Hbz Hxr) as (Rx & Hap & _ & HnQ & HnG).
      apply (Hhyb_out x ltac:(clear - Rx; lia)). intros Hn.
      exact (proj1 (proj2 (proj2 (ncell_fp pz mem0 HI Hdisj c x Hcin Z1 Hn))) Hap). }
    pose proof (HA_pri_step (s_next Lb) E E'' M a mem0 hyb pri' HA0 HawLb Ha'' Hne Hne' Hown_eq
                  ltac:(change (a_with a pri') with aw; rewrite Epz2; exact HIz') Hbase Hmono Hdepf Hext_step Hext_fr) as HAw.
    pose proof (own_pt_with (s_next Lb) E E'' M a mem0 hyb pri' HA0 HawLb Ha'' Hne Hown_eq
                  ltac:(change (a_with a pri') with aw; rewrite Epz2; exact HIz') Hbase Hmono) as Hsub.
    change (a_with a pri') with aw in HAw, Hsub.
    (* [comment removed for export] *)
    assert (HQJ : 1 <= z_qn pz -> 0 <= z_qj pz < 32 /\ z_qj pz < z_j pz 24).
    { intros Hq1. destruct (iz_q _ _ HI) as [(_ & _ & [(Q0 & _)|(_ & Q2 & _)]) Hqj]; [clear - Q0 Hq1; lia | split; [exact Q2 | exact (Hqj Hq1)]]. }
    assert (HGL : 1 <= z_gn pz -> 0 <= z_gl pz < 32 /\ z_gl pz < z_j pz 24).
    { intros Hg1. destruct (iz_gq _ _ HI) as [(_ & _ & _ & _ & _ & _ & _ & _ & [(G0 & _)|(_ & G2 & _)]) Hgl]; [clear - G0 Hg1; lia | split; [exact G2 | exact (Hgl Hg1)]]. }
    assert (Hbat : forall q, 0 <= q < 32 -> q < z_j pz 24 ->
              CHB + ND <= z_sb pz + 103079215104 + 8192 * q \/ z_sb pz + 103079215104 + 8192 * q + 8192 <= CHB).
    { intros q Hq0 Hq1. assert (Hsj : 0 <= sz_tbl c * z_j pz c /\ sz_tbl c * z_j pz c + sz_tbl c <= 262144) by (clear - K0 Hszp Hjn Hnm; nia).
      destruct (Z.eq_dec c 24) as [E24|N24].
      - right. unfold CHB. rewrite E24 in *. change (sz_tbl 24) with 8192. clear - Hq1. lia.
      - assert (D : c <= 23 \/ 25 <= c) by (clear - N24; lia). destruct D as [D|D]; [left | right]; unfold CHB; clear - D Hsj HND Hq0; lia. }
    assert (Hext : a_pri aw <> [] -> ext_sem (pden E'' aw) (uE E'' chl) (uE E'' ndl)).
    { intros _. rewrite Epz2, Ech'', End''. unfold TT. split; [|split].
      - exists c. split; [exact Hcin|]. rewrite (step_sb pz c Hlenz Hcr), (step_j_same pz c Hlenz Hcr). destruct HCHB as (_ & _ & B3).
        split; [unfold CHB; clear - K0 Hszp; nia|]. split; [unfold CHB; clear - HND Hszp; nia | exact B3].
      - rewrite (step_sb pz c Hlenz Hcr), (step_qn pz c Hlenz Hcr), (step_qj pz c Hlenz Hcr). intros Hq1. destruct (HQJ Hq1) as [Q0 Q1]. exact (Hbat _ Q0 Q1).
      - rewrite (step_sb pz c Hlenz Hcr), (step_gn pz c Hlenz Hcr), (step_gl pz c Hlenz Hcr). intros Hg1. destruct (HGL Hg1) as [Q0 Q1]. exact (Hbat _ Q0 Q1). }
    (* [comment removed for export] *)
    assert (Hnew : a_pri aw <> [] -> forall q, In q (x_rngs E'' aw) -> forall x, ~ (uE E'' chl <= x < uE E'' chl + uE E'' ndl /\ in_rg q x)).
    { intros _ q Hq x [X1 X2]. rewrite Ech'', End'' in X1.
      change (x_rngs E'' aw) with (x_rngs E'' a) in Hq. rewrite (x_rngs_agree _ E E'' a HawLb Ha'') in Hq.
      destruct (x_rngs_ext_sem E a mem0 pz (po_ext _ _ _ _ HP0) (proj1 (po_lv _ _ _ _ HP0)) q Hq x X2) as (b0 & z0 & Hs0 & Hr0).
      apply (new_chunk_apart pz mem0 c b0 z0 x HI Hcin Hs0 Hr0). unfold CHB in X1. clear - X1 HND Hszp. nia. }
    pose proof (HA_on_ext_add E'' (with_own M (a_own aw)) aw hyb chl ndl HAw Hext Hnew) as HA'.
    (* [comment removed for export] *)
    set (Y4 := addo_post (addo_post Y2 R2) R1) in *.
    assert (HD11 : DEN ASEGS LIMIT model0 hyb E'' Y4 (with_own M (a_own aw)) ms' model').
    { apply (den_own_set ASEGS LIMIT model0 hyb hyb E'' Y4 M ms' model' (a_own aw) HD10).
      - pose proof Cawf as XW. unfold awf in XW. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [_ XW].
        exact XW.
      - intros w _. reflexivity.
      - intros w Hw. apply Hsub. exact (proj1 (own_pt_agree (s_next Lb) E E'' M w HwfM Ha'') Hw).
      - intros w (q & Hq & Hqw). cbn [with_own sm_own] in Hq.
        assert (Hw0 : own_pt E M w).
        { rewrite (ha_aown _ _ _ _ HAw) in Hq. unfold aown_of in Hq. apply in_app_or in Hq as [Hq|Hq].
          * exists q. split.
            + rewrite Hown_eq, (ha_aown _ _ _ _ HA0). unfold aown_of. apply in_or_app. left. exact Hq.
            + assert (Hpw : pwf (s_next Lb) q = true).
              { pose proof HawLb as XW. unfold awf in XW. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [_ XW].
                rewrite forallb_forall in XW. apply XW. rewrite (ha_aown _ _ _ _ HA0). unfold aown_of. apply in_or_app. left. exact Hq. }
              unfold pwf in Hpw. apply andb_prop in Hpw as [Hp1 Hp2]. rewrite <- (uE_agree _ E E'' _ Hp1 Ha''), <- (uE_agree _ E E'' _ Hp2 Ha''). exact Hqw.
          * assert (Hq' : In q (pri_own aw)) by (change (a_pri aw) with pri' in Hq; destruct pri'; [destruct Hq | exact Hq]).
            pose proof (pri_own_foot E'' aw hyb ltac:(unfold INV_A; rewrite Epz2; exact HIz') q Hq' w Hqw) as Hf.
            unfold pri_foot in Hf. rewrite Epz2 in Hf.
            assert (Hf0 : pri_foot_z pz w).
            { unfold TT, pri_foot_z in *. rewrite (step_ca pz c Hlenz Hcr), (step_sb pz c Hlenz Hcr), (step_sh pz c Hlenz Hcr) in Hf.
              destruct Hf as [Hf|[Hf|[Hf|(c' & Hc' & Hf)]]]; [left; exact Hf | right; left; exact Hf | right; right; left; exact Hf |]. right. right. right. exists c'. split; [exact Hc'|].
              destruct (Z.eq_dec c' c) as [->|Hnc]; [rewrite (step_z_same pz c Hlenz Hcr) in Hf; rewrite Z1; exact Hf|].
              rewrite (step_z_other pz c Hlenz Hcr c' (in_cls_rng c' Hc') Hnc) in Hf. exact Hf. }
            apply (po_own _ _ _ _ HP0 w); [pose proof (pri_foot_rng E a mem0 HI w Hf0) as Pr; clear - Pr; lia | exact Hf0]. }
        pose proof (proj2 (own_pt_agree (s_next Lb) E E'' M w HwfM Ha'') Hw0) as (q0 & Hq0 & Hq0w).
        exact (dn_own _ _ _ _ _ _ _ _ _ HD10 q0 Hq0 w Hq0w). }
    apply (Hk E'' hyb ms' model').
    + apply (agree_mono _ (s_next Lb)); [cbn [Lb np_front s_next]; unfold n0; clear; lia | exact Ha''].
    + intros q Hq w Hw. apply Hfrzn. exists q. split; [exact Hq | exact Hw].
    + exact HD11.
    + intros _. exact HA'.
Qed.
End NPopGNode.
End AcNPopGN.

Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NPopGFirst.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis Hsegb : segs_below_b ASEGS 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved ASEGS).
Hypothesis Hreswf : ivs_wf (segments_reserved ASEGS).

#[using="Hwx Hsegb Hoff Hrespos Hreswf"] Theorem npopg_node_first : forall S M a S' M' a', apost_npopg0 LIMIT S M a = Some (S', M', a') ->
  forall mem0 E0 ms model T, DEN ASEGS LIMIT model0 mem0 E0 S M ms model -> awf (s_next S) a = true -> HA E0 M a mem0 ->
  z_j (pden E0 a) (cls_of (uE E0 (rget (s_regs S) (rk 12)))) = 0 ->
  (forall E' mem0' ms' model', agree (s_next S) E0 E' -> frz_same E0 M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros S M a S' M' a' H mem0 E0 ms model T Hd0 Haw HHA0 Hj00 Hk0.
  unfold apost_npopg0 in H. cbv zeta in H.
  apply obool_some in H as (Hon & H).
  apply obind_some in H as (ND8 & Hnd8 & H). cbv beta in H.
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
  apply andb_prop in Hchk as [Hchk Cfu]. apply andb_prop in Hchk as [Hchk Csep]. apply andb_prop in Hchk as [Hchk Cawf].
  apply andb_prop in Hchk as [Hchk CpX]. apply andb_prop in Hchk as [Hchk CwLg]. apply andb_prop in Hchk as [Hchk CwL].
  apply andb_prop in Hchk as [Hchk Cband]. apply andb_prop in Hchk as [Hchk Cge]. apply andb_prop in Hchk as [Hchk Cjb].
  apply andb_prop in Hchk as [Hchk Csbw]. apply andb_prop in Hchk as [Hchk Cst]. apply andb_prop in Hchk as [Hchk Cro].
  apply andb_prop in Hchk as [Hchk Cwin]. apply andb_prop in Hchk as [Hchk Csphi]. apply andb_prop in Hchk as [Hchk Csplo].
  apply andb_prop in Hchk as [Hchk Cmod]. apply andb_prop in Hchk as [Hchk Cchi]. apply andb_prop in Hchk as [Hchk Cclohi].
  apply andb_prop in Hchk as [Hchk Cclo1]. apply andb_prop in Hchk as [Hchk Cnd8]. apply andb_prop in Hchk as [Hchk Cndhi]. apply andb_prop in Hchk as [Hchk Cndlo].
  apply andb_prop in Hchk as [Hchk Ca3]. apply andb_prop in Hchk as [Hchk Ca1]. apply andb_prop in Hchk as [Cperm Ca0].
  apply lin_eqb_eq in Ca0, Ca1, Ca3. apply Z.leb_le in Cndlo, Cndhi, Cnd8, Cclo1, Cclohi, Cchi, Csplo, Csphi.
  set (SPl := rget (s_regs S) (rk 2)) in *. set (ndl := rget (s_regs S) (rk 12)) in *.
  set (front := firstn 3 (carve_rgs cv)) in *. set (rest := skipn 3 (carve_rgs cv)) in *.
  set (L := np_front S (s_next S) front) in *. set (Sp := np_rest S rest) in *.
  set (n0 := (s_next S + 1)%positive) in *.
  set (clo := tcls (fst (irange (s_facts S) ndl))) in *. set (chi := tcls (snd (irange (s_facts S) ndl))) in *. set (ccs := crange clo chi) in *.
  set (Lg := np_front_f S n0 front [FRange (lvar (s_next S)) clo chi]) in *.
  set (rbg := ladd (p_sb a) (lscale 4294967296 (lvar (s_next S)))) in *.
  set (fag := laddc rbg 3758096384) in *.
  set (Lb := np_front S (n0 + 66) front) in *.
  (* [comment removed for export] *)
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd0)) as (_ & _ & _ & _ & _ & _ & HF00 & _).
  pose proof (irange_sound E0 (s_facts S) ndl HF00) as Rnd0. fold (uE E0 ndl) in Rnd0.
  assert (HND10' : 1 <= uE E0 ndl <= 65536) by (clear - Rnd0 Cndlo Cndhi; lia).
  set (c := cls_of (uE E0 ndl)) in *.
  set (E := upd E0 (s_next S) (wa c)).
  assert (Hag0 : agree (s_next S) E0 E).
  { intros x Hx. unfold E, upd. replace (Pos.eqb x (s_next S)) with false by (symmetry; apply Pos.eqb_neq; clear - Hx; lia). reflexivity. }
  pose proof (den_agree ASEGS LIMIT model0 mem0 E0 E S M ms model Hd0 Hag0) as Hd.
  assert (HwfM0 : sm_wf (s_next S) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd0).
  assert (HHA : HA E M a mem0) by (intros Hon'; exact (HA_on_agree (s_next S) E0 E M a mem0 (HHA0 Hon') HwfM0 Haw Hag0)).
  assert (Hwnd : lwf (s_next S) ndl = true).
  { pose proof CwL as XW. unfold state_wf in XW. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _].
    exact (regs_wf_n_spec _ _ 31 XW 12%nat ltac:(clear; lia)). }
  assert (End0 : uE E ndl = uE E0 ndl) by exact (uE_agree (s_next S) E0 E ndl Hwnd Hag0).
  assert (Epd0 : pden E a = pden E0 a) by exact (pden_agree (s_next S) E0 E a Haw Hag0).
  assert (Hj0 : z_j (pden E a) c = 0) by (rewrite Epd0; exact Hj00).
  assert (Hfzc : forall mem0', frz_same E M mem0 mem0' -> frz_same E0 M mem0 mem0').
  { intros mem0' Hfz' p Hp w Hw. destruct (proj2 (frz_pt_agree (s_next S) E0 E M w HwfM0 Hag0) (ex_intro _ p (conj Hp Hw))) as (q & Hq & Hqw).
    exact (Hfz' q Hq w Hqw). }
  pose proof (fun E' mem0' ms' model' (Ha' : agree (s_next S) E E') (Hfz' : frz_same E M mem0 mem0') =>
                Hk0 E' mem0' ms' model' (agree_trans _ _ _ _ Hag0 Ha') (Hfzc mem0' Hfz')) as Hk.
  clear Hk0 Hj00.
  assert (EVC : E (s_next S) = wa c) by (unfold E, upd; rewrite Pos.eqb_refl; reflexivity).
  assert (HND10 : 1 <= uE E ndl <= 65536) by (rewrite End0; exact HND10').
  assert (Ec : c = tcls (uE E0 ndl)) by exact (tcls_cls_of _ HND10').
  destruct (tcls_spec (uE E0 ndl) HND10') as [Hcr HND0']. rewrite <- Ec in Hcr, HND0'.
  assert (HND0 : sz_tbl (c - 1) < uE E ndl <= sz_tbl c) by (rewrite End0; exact HND0').
  assert (Hccs : In c ccs).
  { apply in_crange. rewrite Ec. unfold clo, chi. split; apply tcls_mono; clear - Rnd0 Cndlo Cndhi HND10'; lia. }
  assert (Hclc : clo <= c <= chi) by (apply crange_rng; exact Hccs).
  pose proof (rng_in_cls c Hcr) as Hcin.
  pose proof (HHA Hon) as HA0.
  assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hlen; discriminate).
  pose proof (ha_pri _ _ _ _ HA0 Hne) as HP0.
  (* [comment removed for export] *)
  pose proof (den_carve ASEGS LIMIT model0 mem0 E S M ms model _ _ _ cv Hd Hcv Cperm) as Hd1.
  assert (EQ1 : with_rgs S (carve_rgs cv) = mrg L Sp).
  { destruct S as [pc0 rg0 rgs0 fs0 nx0 rv0]. cbn [s_pc s_resv] in Hpc, Hrs. subst pc0 rv0.
    unfold with_rgs, mrg, L, Sp, np_front, np_rest. cbn [s_pc s_regs s_rgs s_facts s_next s_resv]. unfold front, rest. rewrite firstn_skipn. reflexivity. }
  rewrite EQ1 in Hd1.
  (* [comment removed for export] *)
  assert (HdG : DEN ASEGS LIMIT model0 mem0 E (mrg Lg Sp) M ms model).
  { pose proof (den_bump ASEGS LIMIT model0 mem0 E _ M ms model n0 Hd1 ltac:(cbn [mrg s_next L np_front]; unfold n0; clear; lia)) as HdB.
    pose proof (den_facts ASEGS LIMIT model0 mem0 E _ M ms model (s_facts (mrg Lg Sp)) HdB) as HdF.
    assert (EQg : with_facts (bump (mrg L Sp) n0) (s_facts (mrg Lg Sp)) = mrg Lg Sp) by reflexivity.
    rewrite <- EQg. apply HdF. intros E' Ha' HF'. cbn [mrg s_facts Lg np_front_f app]. constructor.
    - cbn [fact_ok]. rewrite lden_lvar, <- (Ha' (s_next S) ltac:(cbn [bump s_next]; unfold n0; clear; lia)), EVC, u_wa_small by (clear - Hcr; lia). exact Hclc.
    - cbn [bump mrg s_facts L np_front app] in HF'. exact HF'. }
  (* [comment removed for export] *)
  pose proof (po_inv _ _ _ _ HP0) as HI. unfold INV_A in HI. set (pz := pden E a) in *.
  pose proof (tg_pg_disj LIMIT model0 mem0 E S M ms model a mem0 Hd HP0) as Hdisj. fold pz in Hdisj.
  pose proof (az_geo pz mem0 HI) as G.
  destruct (cls_tbl c Hcin) as (Hszp & Hs8 & Hsz8 & Hnw & Hnm & Hmc).
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HRG & _ & HF0 & _).
  assert (Ej : uE E (p_j a c) = z_j pz c) by (symmetry; apply zn_pden).
  assert (Eca : uE E (p_ca a) = z_ca pz) by (symmetry; apply zn_pden).
  assert (Esb : uE E (p_sb a) = z_sb pz) by (symmetry; apply zn_pden).
  assert (Hjhi : z_j pz c + mc_tbl c / 2 + 1 <= 262144 / sz_tbl c).
  { rewrite forallb_forall in Cjb. pose proof (Cjb c Hccs) as X1. apply Z.leb_le in X1.
    pose proof (irange_sound E (s_facts S) (p_j a c) HF0) as X. fold (uE E (p_j a c)) in X. rewrite Ej in X. clear - X X1. lia. }
  destruct (iz_cls _ _ HI c Hcin) as [(_ & Z0 & HV & HSW)|(J1 & _)]; [|clear - J1 Hj0; lia].
  pose proof (iz_st _ _ HI) as HST.
  (* [comment removed for export] *)
  pose proof (irange_sound E (s_facts S) SPl HF0) as Rsp. fold (uE E SPl) in Rsp.
  pose proof (irange_sound E (s_facts S) ndl HF0) as Rnd. fold (uE E ndl) in Rnd.
  assert (Hal : uE E SPl mod 16 = 0) by (pose proof (fact_implied_ok E _ _ HF0 Cmod) as X; cbn [fact_ok] in X; exact X).
  assert (HND : sz_tbl (c - 1) < uE E ndl <= sz_tbl c) by exact HND0.
  assert (HND1 : 1 <= uE E ndl <= 65536) by exact HND10.
  (* [comment removed for export] *)
  assert (Hjlo : forallb (fun c0 => Z.ltb 0 (fst (irange (s_facts S) (p_j a c0)))) ccs = false).
  { destruct (forallb (fun c0 => Z.ltb 0 (fst (irange (s_facts S) (p_j a c0)))) ccs) eqn:Efb; [|reflexivity]. exfalso.
    rewrite forallb_forall in Efb. pose proof (Efb c Hccs) as X1. apply Z.ltb_lt in X1.
    pose proof (irange_sound E (s_facts S) (p_j a c) HF0) as X. fold (uE E (p_j a c)) in X. rewrite Ej, Hj0 in X. clear - X X1. lia. }
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
  { cbn [mrg s_rgs L Sp np_front np_rest] in HRG1. apply Forall_app in HRG1. exact (proj2 HRG1). }
  (* [comment removed for export] *)
  unfold fu_tls_ok in Ctls. cbn [Sp np_rest s_rgs s_regs] in Ctls.
  set (TPl := rget (s_regs S) (rk 4)) in *.
  destruct (rdw IMGP rest (lconst 935460) 4) as [Kl|] eqn:WK; [|discriminate].
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
  assert (Ebw : bv_unsigned (lden E (laddc SPl (-2048))) = SP - 2048) by (rewrite lden_laddc; fold (uE E SPl); fold SP; rewrite u_small64; unfold two64; clear - HSPr; lia).
  assert (HSTK : stk_ok SEGS mr (wa SP) 2048).
  { intros a0 k Ha Hk'. rewrite u_wa_small in Ha, Hk' by (clear - HSPr; lia). apply store_ok_of_all; [pose proof (bv_unsigned_in_range _ a0); clear - Ha Hk' HSPr H; lia|].
    intros x Hx. pose proof (bv_unsigned_in_range _ x) as Rx.
    destruct (rg_rw_pt _ _ _ (bv_unsigned x) Rw eq_refl) as [_ W].
    { cbn [rg_base]. rewrite Ebw. unfold rsz. cbn [rg_size]. rewrite lden_lconst, u_small64 by (unfold two64; lia). clear - Ha Hk' Hx. lia. }
    rewrite Z_to_bv_bv_unsigned in W. exact W. }
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
    pose proof (OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcConvA.AcRdw.lin_off_u E mr PTl Rp o0 160 HRp0 Hl C1 ltac:(rewrite Ez0; exact C2) ltac:(lia)) as Ea.
    exists Rp. split; [exact HRp|]. fold PT in Ea. rewrite Ea, Ez0. clear - C1 C2. lia. }
  assert (HPTband : 1 <= PT /\ PT + 160 + 4320 <= SP).
  { rewrite existsb_l_eq in Cgb. apply existsb_exists in Cgb as (g & Hg & Hc0). cbn [Sp np_rest s_facts] in Hc0.
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
    specialize (Hou Rp ltac:(cbn [mrg s_rgs L Sp np_front np_rest]; apply in_or_app; right; exact HRp)).
    destruct (Hvf w Hv) as (_ & _ & F4). rewrite u_small64 in Hou by (unfold two64; clear - F4; lia). unfold uE in Pp1, Pp2. clear - Hou Hw Pp1 Pp2. lia. }
  (* [comment removed for export] *)
  set (regs := ms_regs ms) in *.
  assert (R2 : getr regs (Z_to_bv 5 2) = wa SP).
  { change regs with (ms_regs (restrict (Hof E M model) ms)). rewrite (mrg_reg0 E L Sp _ (Z_to_bv 5 2) _ Hd10 eq_refl). unfold wa, SP, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R10 : getr regs (Z_to_bv 5 10) = wa 923480).
  { change regs with (ms_regs (restrict (Hof E M model) ms)). rewrite (mrg_reg0 E L Sp _ (Z_to_bv 5 10) _ Hd10 Ca0). rewrite lden_lconst. reflexivity. }
  assert (R11 : getr regs (Z_to_bv 5 11) = wa CA).
  { change regs with (ms_regs (restrict (Hof E M model) ms)). rewrite (mrg_reg0 E L Sp _ (Z_to_bv 5 11) _ Hd10 Ca1). unfold wa. rewrite <- Eca. unfold uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R12 : getr regs (Z_to_bv 5 12) = wa (uE E ndl)).
  { change regs with (ms_regs (restrict (Hof E M model) ms)). rewrite (mrg_reg0 E L Sp _ (Z_to_bv 5 12) _ Hd10 eq_refl). unfold wa, uE. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R13 : getr regs (Z_to_bv 5 13) = wa 8).
  { change regs with (ms_regs (restrict (Hof E M model) ms)). rewrite (mrg_reg0 E L Sp _ (Z_to_bv 5 13) _ Hd10 Ca3). rewrite lden_lconst. reflexivity. }
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
  assert (HCA' : ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6529232 <= CA) /\ CA mod 16 = 0 /\ CA + 4096 <= SP - 2048) by (split; [exact Pca|]; split; [exact Aca|]; clear - B0 BT; lia).
  assert (HSB' : 17594333495296 <= SB /\ SB mod 4096 = 0 /\ SB + 137438953472 + 4096 <= SP - 2048).
  { pose proof (proj2 (iz_sb _ _ HI)) as X2. fold pz SB in X2. clear - B0 BP X2. split; [lia|]. split; [exact X2 | lia]. }
  assert (HSEP' : CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) by (clear - T1 B0; lia).
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
  assert (HO : objs_ok_p (SP - 2048) TT RIv TP TSDA PT).
  { unfold objs_ok_p, t_place. destruct (PTsep (SB + 137438953472) 4096 ltac:(lia) ltac:(intros w Hw; right; left; exact Hw)) as [X|X];
      unfold RIv; clear - HSPr B0 BT BP Pca T1 Hcr CT5 CT6 CT7 CT8 CT1 CT2 HPTband X; lia. }
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
    { cbn [mrg s_rgs L Sp np_front np_rest]. rewrite nth_error_app2 by (rewrite Hlf; clear; lia). rewrite Hlf. replace (3 + ip - 3)%nat with ip by (clear; lia). exact Hip. }
    assert (N2 : nth_error (s_rgs (mrg L Sp)) 2 = Some (RG (laddc (p_tg a) 2872) (lconst 16) RW cs)).
    { cbn [mrg s_rgs L Sp np_front np_rest]. rewrite nth_error_app1 by (rewrite Hlf; clear; lia). exact Pst. }
    pose proof (rgs_disj_nth E _ (3 + ip)%nat 2%nat _ _ HDJ1 ltac:(clear; lia) N1 N2) as Hdj. unfold rg_disj in Hdj. cbv zeta in Hdj. cbn [rg_base] in Hdj.
    unfold rsz in Hdj at 2. cbn [rg_size] in Hdj. rewrite lden_lconst, (u_small64 16) in Hdj by (unfold two64; lia).
    fold (uE E (laddc (p_tg a) 2872)) in Hdj. rewrite uE_laddc_z in Hdj by (rewrite Etg; fold TT; unfold two64; clear - B0; lia). rewrite Etg in Hdj. fold TT in Hdj.
    fold (uE E (rg_base Rp)) in Hdj. clear - Hdj Pp1 Pp2. lia. }
  (* [comment removed for export] *)
  assert (HENV : forall x, gENVC TP K TSDA PT x -> ~ gCHC CA c SB SP TT x).
  { intros x He Hc0. unfold gENVC in He. unfold gCHC in Hc0. cbv zeta in Hc0. fold SHv SHFv in Hc0. rewrite ESHv, ESHFv in Hc0.
    assert (Hx3 : (65536 <= x < 6529024) \/ PT + 152 <= x < PT + 160) by (clear - He CT1 CT2 CT5 CT6 CT7 CT8; lia). clear He.
    destruct Hx3 as [Hx3|Hx3].
    - unfold RBv, FAv in Hc0. clear - Hc0 Hx3 HSPr Pca B0 S1 Hcr. lia.
    - assert (Hpt : PT <= x < PT + 160) by (clear - Hx3; lia).
      destruct Hc0 as [Hc0|[Hc0|[Hc0|[Hc0|Hc0]]]].
      + clear - Hc0 Hx3 HPTband. lia.
      + apply (HPTv x Hpt). left. clear - Hc0. lia.
      + apply (HPTv x Hpt). right. left. clear - Hc0 Hcr. lia.
      + clear - Hc0 Hx3 HPTst. lia.
      + apply (HPTv x Hpt). right. right. unfold RBv, FAv. clear - Hc0. lia. }
  (* [comment removed for export] *)
  unfold sb_words_ok in Csbw. destruct (rdw IMGP (s_rgs S) (lconst 923512) 8) as [l1|] eqn:W1; [|discriminate].
  destruct (rdw IMGP (s_rgs S) (lconst 923528) 8) as [l2|] eqn:W2; [|discriminate].
  apply andb_prop in Csbw as [Q1 Q2]. apply lin_eqb_eq in Q1, Q2. subst l1 l2.
  pose proof (rdw_sound IMGP IMGP_ok E _ (s_rgs S) (lconst 923512) 8 _ HRG ltac:(lia) W1) as RSB.
  pose proof (rdw_sound IMGP IMGP_ok E _ (s_rgs S) (lconst 923528) 8 _ HRG ltac:(lia) W2) as RRIB.
  rewrite uE_lc in RSB, RRIB by lia. rewrite Esb in RSB.
  assert (Erip : uE E (l_rip a) = z_sb pz + 137438953472).
  { unfold l_rip. rewrite uE_laddc2 by (rewrite ?Esb; unfold two64; clear - B0; fold SB; lia). rewrite Esb. reflexivity. }
  rewrite Erip in RRIB.
  fold SB in RSB, RRIB.
  (* [comment removed for export] *)
  set (fx1 := mkFP (ms_fregs ms) (ms_fcsr ms)).
  set (ND := uE E ndl) in *.
  assert (Hcls : c = cls_of ND) by (rewrite End0; reflexivity).
  assert (HSPp : 2^46 + 4096 <= SP <= 2^47 /\ SP mod 16 = 0) by (split; [clear - HSPr; lia | exact Hal]).
  assert (HstA : exists R1 mA, msteps SEGS (@mkst fx1 regs (wa 0x43ce8) mr (ms_rom ms)) (@mkst fx1 R1 (wa 0x73c44) mA (ms_rom ms)) /\
            EC R1 RBv /\ getr R1 (Z_to_bv 5 (Z.of_nat 1)) = wa 481796 /\ getr R1 (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 400) /\
            getr R1 (Z_to_bv 5 (Z.of_nat 8)) = wa 262144 /\ getr R1 (Z_to_bv 5 (Z.of_nat 21)) = wa (sz_tbl c) /\ getr R1 (Z_to_bv 5 (Z.of_nat 22)) = wa 923480 /\
            (forall k, In k [3; 4]%nat -> getr R1 (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))) /\
            gMA_OK mr mA regs SP CA c RIv RBv FAv /\
            ((forall i, 1 <= i <= 31 -> rd mA (CA + 80 * i + 4) 4 (mc_tbl i) /\ rd mA (CA + 80 * i + 8) 8 (sz_tbl i)) \/
             (forall x, CA <= x < CA + 2592 -> mA (wa x) = mr (wa x))) /\
            (forall x, 0 <= x < 2^64 -> ~ (SP - 2048 <= x < SP) -> (forall i, 1 <= i <= 31 -> ~ (CA + 80 * i + 4 <= x < CA + 80 * i + 16)) ->
               ~ (RIv <= x < RIv + 8) -> mA (wa x) = mr (wa x))).
  { assert (R2b : getr regs (2%bv : reg) = wa SP) by (replace (2%bv : reg) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity); exact R2).
    assert (R10b : getr regs (10%bv : reg) = wa 923480) by (replace (10%bv : reg) with (Z_to_bv 5 10) by (apply bv_eq; reflexivity); exact R10).
    assert (R11b : getr regs (11%bv : reg) = wa CA) by (replace (11%bv : reg) with (Z_to_bv 5 11) by (apply bv_eq; reflexivity); exact R11).
    assert (R12b : getr regs (12%bv : reg) = wa ND) by (replace (12%bv : reg) with (Z_to_bv 5 12) by (apply bv_eq; reflexivity); exact R12).
    assert (R13b : getr regs (13%bv : reg) = wa 8) by (replace (13%bv : reg) with (Z_to_bv 5 13) by (apply bv_eq; reflexivity); exact R13).
    pose proof (FW (923520, 4%nat, 4294967295) (nth_error_In FU_WORDS 5 eq_refl)) as W1'. cbn [fst snd] in W1'.
    pose proof (FW (923536, 1%nat, 0) (nth_error_In FU_WORDS 6 eq_refl)) as W2'. cbn [fst snd] in W2'.
    pose proof (FW (904176, 8%nat, 1525856) (nth_error_In FU_WORDS 0 eq_refl)) as W3'. cbn [fst snd] in W3'.
    pose proof (FW (1525856, 8%nat, 4096) (nth_error_In FU_WORDS 1 eq_refl)) as W4'. cbn [fst snd] in W4'.
    pose proof (FW (904192, 8%nat, 1534184) (nth_error_In FU_WORDS 2 eq_refl)) as W5'. cbn [fst snd] in W5'.
    pose proof (FW (1534444, 1%nat, 0) (nth_error_In FU_WORDS 4 eq_refl)) as W6'. cbn [fst snd] in W6'.
    destruct Vic as [(Vmc & sz0 & Hsz0 & Vsz)|(Vmc & Vsz)].
    - (* [comment removed for export] *)
      assert (Imc : rd mr (CA + 80 * c + 4) 4 0).
      { apply (rd_frame mem0); [clear - B0 Hcr; lia | cbn; clear - B0 Hcr; lia | intros x Hx; cbn in Hx; apply Hmr_foot; left; clear - Hx Hcr; lia | exact Vmc]. }
      assert (Isz : rd mr (CA + 80 * c + 8) 8 sz0).
      { apply (rd_frame mem0); [clear - B0 Hcr; lia | cbn; clear - B0 Hcr; lia | intros x Hx; cbn in Hx; apply Hmr_foot; left; clear - Hx Hcr; lia | exact Vsz]. }
      destruct (@gstageA fx1 (ms_rom ms) mr regs CA ND c SB SP sz0 st Hcls HND1 R2b HSPp HSTK R10b R11b R12b R13b HCA' HSB' HSEP' (conj Hsz0 Hst)
                  Icnt Imc Isz Ist Iwc Iri Iwri RSB RRIB W1' W2' W3' W4' W5' W6') as (R1 & mA & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
      exists R1, mA. repeat (split; [assumption|]). split; [left; exact A10 | exact A11].
    - (* [comment removed for export] *)
      assert (Imc : rd mr (CA + 80 * c + 4) 4 (mc_tbl c)).
      { apply (rd_frame mem0); [clear - B0 Hcr; lia | cbn; clear - B0 Hcr; lia | intros x Hx; cbn in Hx; apply Hmr_foot; left; clear - Hx Hcr; lia | exact Vmc]. }
      assert (Isz : rd mr (CA + 80 * c + 8) 8 (sz_tbl c)).
      { apply (rd_frame mem0); [clear - B0 Hcr; lia | cbn; clear - B0 Hcr; lia | intros x Hx; cbn in Hx; apply Hmr_foot; left; clear - Hx Hcr; lia | exact Vsz]. }
      destruct (@gstageA' fx1 (ms_rom ms) mr regs CA ND c SB SP st Hcls HND1 R2b HSPp HSTK R10b R11b R12b R13b HCA' HSB' HSEP' Hst
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
  assert (Hpc0 : ms_pc_val ms = wa 0x43ce8) by (destruct Hd10 as (X & _); cbn [mrg s_pc L np_front] in X; exact X).
  rewrite <- Hpc0 in A1.
  assert (Est : uE E (laddc (p_tg a) 2872) = TT + 2872).
  { rewrite uE_laddc_z by (rewrite Etg; fold TT; unfold two64; clear - B0; lia). rewrite Etg. reflexivity. }
  set (OWN_A := fun x : Z => (exists i, 1 <= i <= 31 /\ CA + 80 * i + 4 <= x < CA + 80 * i + 16) \/ RIv <= x < RIv + 8).
  assert (HAsp : 2048 <= uE E SPl <= 2^47) by (fold SP; clear - HSPr; lia).
  assert (HAst : uE E (laddc (p_tg a) 2872) + 16 <= 2^47) by (rewrite Est; clear - B0; lia).
  assert (HAown : forall x, 0 <= x < 2^64 -> OWN_A x -> own_pt E M x /\ outside E (s_rgs (mrg L Sp)) (wa x) /\ ~ frz_pt E M x).
  { intros x Hx HO1. apply Hvown. destruct HO1 as [(i & Hi & HO1)|HO1]; [left; clear - Hi HO1; lia | right; left; unfold RIv in HO1; clear - HO1 Hcr; lia]. }
  assert (HAfr : forall x, 0 <= x < 2^64 -> ~ (uE E SPl - 2048 <= x < uE E SPl) -> ~ (uE E (laddc (p_tg a) 2872) <= x < uE E (laddc (p_tg a) 2872) + 16) -> ~ OWN_A x ->
            mA (wa x) = mr (wa x)).
  { intros x Hx Hw _ HO1. fold SP in Hw. apply (A11 x Hx Hw).
    - intros i Hi Hc0. apply HO1. left. exists i. split; [exact Hi | exact Hc0].
    - intros Hc0. apply HO1. right. exact Hc0. }
  assert (HAgr : mem_grows mr mA) by (destruct A9 as (_ & _ & _ & _ & _ & _ & Hg); exact Hg).
  apply (den_run_app_x cfg LIMIT model0 Hwx mem0 Lg Sp E M ms model T SPl (laddc (p_tg a) 2872) 0%nat 2%nat cw cs 0x73c44 K34
           [3; 4]%nat R1 mA OWN_A 2048 ltac:(lia) HdG CwLg eq_refl Pw Pst HAsp HAst k34_cases A1 A8 HAown HAfr HAgr).
  intros E1 ms1 model1 HD1 Ha1g Hfz1 Hrr1 Hvis1 HH1 Hrm1.
  assert (Ha1 : agree (s_next S) E E1) by (apply (agree_mono _ n0); [unfold n0; clear; lia | exact Ha1g]).
  set (Lh1 := hand_post Lg 0x73c44 K34 [0%nat; 2%nat]) in *.
  set (L1 := ecall_tpl Lg [0%nat; 2%nat] rbg) in *.
  assert (HwfM : sm_wf (s_next L) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd1).
  pose proof (awf_pri _ a Haw) as Hwpri.
  assert (Hagr1g : forall E'', agree (s_next (mrg Lh1 Sp)) E1 E'' -> agree n0 E E'').
  { intros E'' Ha''. apply (agree_trans _ E E1 E''); [exact Ha1g |
      apply (agree_mono _ (s_next (mrg Lh1 Sp))); [cbn [mrg Lh1 hand_post Lg np_front_f s_next]; clear; lia | exact Ha'']]. }
  assert (Hagr1 : forall E'', agree (s_next (mrg Lh1 Sp)) E1 E'' -> agree (s_next S) E E'').
  { intros E'' Ha''. apply (agree_mono _ n0); [unfold n0; clear; lia | exact (Hagr1g E'' Ha'')]. }
  assert (Evc : uE E (lscale 4294967296 (lvar (s_next S))) = 4294967296 * c).
  { unfold uE. rewrite lden_lscale, lden_lvar, EVC. rewrite (u_wa_small c) by (clear - Hcr; lia). apply u_small64. unfold two64. clear - Hcr. lia. }
  assert (Erb : uE E rbg = RBv).
  { unfold rbg. rewrite uE_ladd_z by (rewrite Esb, Evc; unfold two64; clear - B0 Hcr; lia). rewrite Esb, Evc. reflexivity. }
  assert (Hwrb : lwf n0 rbg = true).
  { unfold rbg. apply lwf_ladd; [apply (lwf_mono' (s_next S)); [unfold n0; clear; lia | exact (lwf_p_nth _ a 0 Hwpri)] |
      apply lwf_lscale; apply lwf_lvar; unfold n0; clear; lia]. }
  assert (HDr1 : DEN ASEGS LIMIT model0 (ms_mem ms1) E1 (mrg L1 Sp) M ms1 model1).
  { change (mrg L1 Sp) with (with_regs_t (mrg Lh1 Sp) (s_regs L1)).
    apply den_regs_eq; [exact HD1|]. intros E'' Ha'' r.
    pose proof (dn_sden _ _ _ _ _ _ _ _ _ HD1 E'' Ha'') as (_ & _ & _ & Hregs & _).
    rewrite <- (Hregs r). cbn [restrict ms_regs]. rewrite Hrr1.
    unfold L1, ecall_tpl. fold Lh1. apply (with_regs_den E'' R1).
    - intros r'. pose proof (Hregs r') as X. cbn [restrict ms_regs mrg s_regs] in X. rewrite Hrr1 in X. symmetry. exact X.
    - destruct A2 as (Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q17).
      assert (Hlrb : lden E'' rbg = wa RBv).
      { rewrite (lden_agree_wf n0 E E'' rbg Hwrb (Hagr1g E'' Ha'')).
        rewrite <- (Z_to_bv_bv_unsigned _ (lden E rbg)). fold (uE E rbg). rewrite Erb. reflexivity. }
      repeat (constructor; [split; [intros Hc0; vm_compute in Hc0; discriminate | cbn [fst snd]; rewrite ?lden_lconst; first [rewrite Hlrb; symmetry; exact Q10 | symmetry; assumption]] |]).
      constructor. }
  (* [comment removed for export] *)
  assert (Ege : snd gP = GE) by exact (gkind_eqb_GE _ Cge).
  assert (Eu1 : uE E1 rbg = RBv) by (rewrite (uE_agree n0 E E1 _ Hwrb Ha1g); exact Erb).
  assert (HbwS : bases_wf (s_next L) (s_rgs (mrg L Sp)) = true) by exact (dn_bases _ _ _ _ _ _ _ _ _ Hd1).
  assert (Hsh1 : shape (s_rgs (mrg L1 Sp)) = shape (s_rgs (mrg L Sp))).
  { cbn [mrg s_rgs]. unfold L1, ecall_tpl. rewrite with_regs_rgs. unfold hand_post. cbn [s_rgs]. unfold shape. rewrite !map_app. f_equal.
    pose proof (empty_at_shape [0%nat; 2%nat] (s_rgs Lg) 0) as Hs. unfold shape in Hs. exact Hs. }
  assert (Hout1 : forall x, outside E (s_rgs (mrg L Sp)) (wa x) -> outside E1 (s_rgs (mrg L1 Sp)) (wa x)).
  { intros x Hx. apply (outside_shape E1 (s_rgs (mrg L Sp))); [exact Hsh1|]. exact (proj1 (outside_agree (s_next L) E E1 _ _ HbwS Ha1) Hx). }
  assert (Hw64 : forall w, own_pt E M w -> 0 <= w < two64).
  { intros w Hw0. destruct (Z_lt_le_dec w two64) as [X|X].
    - destruct Hw0 as (q & Hq & Hqw). pose proof (uE_range E (fst q)) as Rq. clear - Hqw Rq X. lia.
    - exfalso. destruct (ha_ownx _ _ _ _ HA0 w (own_pt_a_M E M a w Hown_eq Hw0)) as [Dc|[_ Pf]].
      + destruct HA0 as [(nq0 & F0 & st0 & I0 & _) _ _ _ _ _ _]. destruct I0 as [_ _ _ D1r _ _ _ _ _ B1r _ _ _].
        unfold dcov in Dc. unfold two64 in X. clear - Dc X D1r B1r. lia.
      + pose proof (pri_foot_rng E a mem0 HI w Pf) as Rpf. unfold two64 in X. clear - Rpf X. lia. }
  assert (HinPG : forall x, RBv <= x < RBv + 262144 \/ FAv <= x < FAv + 262144 -> z_pg pz <= x < z_pg pz + PG_SIZE).
  { intros x Hx. unfold RBv, FAv, PG_SIZE in *. clear - Hx B0 Hcr. lia. }
  assert (Hc1nr : forall fl, arg (mrg L1 Sp) 3 = Some fl -> mmap_noreserve_b (Z_to_bv 64 fl) = false).
  { intros fl Hfl. assert (Efl : fl = 50) by (vm_compute in Hfl; injection Hfl as <-; reflexivity). rewrite Efl. reflexivity. }
  assert (Hc1top : uE E1 rbg + 262144 <= 2^47) by (rewrite Eu1; unfold RBv; clear - B0 Hcr; lia).
  assert (Hc1rg : forall R0, In R0 (s_rgs (mrg L1 Sp)) -> forall w, uE E1 (rg_base R0) <= w < uE E1 (rg_base R0) + rsz E1 R0 ->
            ~ (uE E1 rbg <= w < uE E1 rbg + 262144)).
  { intros R0 HR0 w Hw Hc0. rewrite Eu1 in Hc0.
    pose proof (Hout1 w (Hvout w ltac:(clear - Hc0; lia))) as Hou. unfold outside in Hou. rewrite Forall_forall in Hou. specialize (Hou R0 HR0).
    rewrite u_wa_small in Hou by (unfold RBv in Hc0; clear - Hc0 B0 Hcr; lia). unfold uE in Hw. clear - Hou Hw Hc0. lia. }
  assert (Hc1own : forall w, own_pt E1 M w -> ~ (uE E1 rbg <= bv_unsigned (Z_to_bv 64 w) < uE E1 rbg + 262144)).
  { intros w Hw Hc0. rewrite Eu1 in Hc0.
    assert (Hw0 : own_pt E M w) by exact (proj1 (own_pt_agree (s_next L) E E1 M w HwfM Ha1) Hw).
    rewrite u_small64 in Hc0 by exact (Hw64 w Hw0).
    destruct (virgin_not_own LIMIT model0 mem0 E S M ms model a Hd HA0 Hne Hown_eq c Hcin Z0 w Hw0) as [N1 _]. apply N1. exact Hc0. }
  assert (Hc1frz : forall w, frz_pt E1 M w -> ~ (uE E1 rbg <= w < uE E1 rbg + 262144)).
  { intros w Hw Hc0. rewrite Eu1 in Hc0.
    assert (Hw0 : frz_pt E M w) by exact (proj1 (frz_pt_agree (s_next L) E E1 M w HwfM Ha1) Hw).
    exact (pg_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne w (HinPG w ltac:(left; exact Hc0)) Hw0). }
  apply (den_commit_own cfg LIMIT model0 Hwx Hsegb Hoff Hrespos Hreswf (ms_mem ms1) (mrg L1 Sp) E1 M ms1 model1 T rbg jP gP HDr1
           eq_refl eq_refl Cfk1 HgP Ege Hc1nr eq_refl Hc1top Hc1rg Hc1own Hc1frz).
  intros ms2 model2 Hms2 HDc1.
  (* [comment removed for export] *)
  set (Rro0 := RG (lconst 65536) (lconst zro) RO TEmpty) in *.
  set (VOWN := fun x : Z => CA - 128 <= x < CA + 2592 \/ SB + 137438953472 <= x < SB + 137438953472 + 4096 \/
                           SH + 536870912 * c <= x < SH + 536870912 * c + 32768 \/
                           SH + 536870912 * c + 469762048 <= x < SH + 536870912 * c + 469762048 + 32768).
  set (COV := fun x : Z => (exists R0, (R0 = Rro0 \/ In R0 rest) /\ uE E (rg_base R0) <= x < uE E (rg_base R0) + rsz E R0) \/
                           SP - 2048 <= x < SP \/ TT + 2872 <= x < TT + 2888 \/ VOWN x).
  assert (HwSP : lwf (s_next S) SPl = true).
  { pose proof CwL as X. unfold state_wf in X. apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. apply andb_prop in X as [X _].
    cbn [L np_front s_regs s_next] in X. exact (regs_wf_n_get _ _ 31 X 2%nat ltac:(lia)). }
  assert (HwTG : lwf (s_next S) (p_tg a) = true) by exact (lwf_p_nth _ a 4 Hwpri).
  assert (Hcov_vis : forall Ei Li Mi msi modeli m0i c0 c2, DEN ASEGS LIMIT model0 m0i Ei (mrg Li Sp) Mi msi modeli -> agree (s_next S) E Ei ->
            nth_error (s_rgs Li) 0 = Some (RG (laddc SPl (-2048)) (lconst 2048) RW c0) -> nth_error (s_rgs Li) 1 = Some Rro0 ->
            nth_error (s_rgs Li) 2 = Some (RG (laddc (p_tg a) 2872) (lconst 16) RW c2) ->
            (forall p, In p (sm_own M) -> In p (sm_own Mi)) ->
            forall x, COV x -> Hof Ei Mi modeli (wa x) = false).
  { intros Ei Li Mi msi modeli m0i c0 c2 HDi Hai Q0 Q1 Q2 Hsub x Hc.
    assert (HinL : forall k R0, nth_error (s_rgs Li) k = Some R0 -> In R0 (s_rgs (mrg Li Sp))).
    { intros k0 R0 Hk0. cbn [mrg s_rgs]. apply in_or_app. left. exact (nth_error_In _ _ Hk0). }
    destruct Hc as [(R0 & HR0 & Hx)|[Hx|[Hx|Hx]]].
    - assert (HR0' : In R0 (s_rgs (mrg L Sp))).
      { cbn [mrg s_rgs L Sp np_front np_rest]. apply in_or_app. destruct HR0 as [->|HR0]; [left; exact (nth_error_In _ _ Pro) | right; exact HR0]. }
      unfold bases_wf in HbwS. rewrite forallb_forall in HbwS. destruct (andb_prop _ _ (HbwS R0 HR0')) as [Hb1 Hb2].
      apply (den_rg_vis LIMIT model0 m0i Ei (mrg Li Sp) Mi msi modeli R0 x HDi).
      + destruct HR0 as [->|HR0]; [exact (HinL 1%nat _ Q1) | cbn [mrg s_rgs Sp np_rest]; apply in_or_app; right; exact HR0].
      + unfold uE, rsz in *. rewrite (lden_agree_wf _ E Ei _ Hb1 Hai), (lden_agree_wf _ E Ei _ Hb2 Hai). exact Hx.
    - apply (den_rg_vis LIMIT model0 m0i Ei (mrg Li Sp) Mi msi modeli _ x HDi (HinL 0%nat _ Q0)). cbn [rg_base]. unfold rsz. cbn [rg_size].
      rewrite lden_lconst, (u_small64 2048) by (unfold two64; lia). unfold uE. rewrite (lden_agree_wf _ E Ei _ (lwf_laddc _ _ _ HwSP) Hai).
      rewrite Ebw. clear - Hx. lia.
    - apply (den_rg_vis LIMIT model0 m0i Ei (mrg Li Sp) Mi msi modeli _ x HDi (HinL 2%nat _ Q2)). cbn [rg_base]. unfold rsz. cbn [rg_size].
      rewrite lden_lconst, (u_small64 16) by (unfold two64; lia). unfold uE. rewrite (lden_agree_wf _ E Ei _ (lwf_laddc _ _ _ HwTG) Hai).
      fold (uE E (laddc (p_tg a) 2872)). rewrite Est. clear - Hx. lia.
    - destruct (Hvown x Hx) as ((p & Hp & Hpw) & _).
      pose proof (sm_wf_own _ M HwfM) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw p Hp) as [Hf1 Hf2].
      cbn [L np_front s_next] in Hf1, Hf2.
      refine (proj1 (dn_own _ _ _ _ _ _ _ _ _ HDi p (Hsub p Hp) x _)).
      unfold uE in *. rewrite (lden_agree_wf _ E Ei _ Hf1 Hai), (lden_agree_wf _ E Ei _ Hf2 Hai). exact Hpw. }
  (* [comment removed for export] *)
  assert (HENVrg : forall x, gENVC TP K TSDA PT x -> exists R0, (R0 = Rro0 \/ In R0 rest) /\ uE E (rg_base R0) <= x < uE E (rg_base R0) + rsz E R0).
  { intros x He. unfold gENVC in He.
    assert (Hnum : forall lo hi, In (lo, hi) ENVC_RNG -> lo <= x < hi -> exists R0, (R0 = Rro0 \/ In R0 rest) /\ uE E (rg_base R0) <= x < uE E (rg_base R0) + rsz E R0).
    { intros lo hi Hin Hx. unfold envc_ok in Cenv. rewrite forallb_forall in Cenv. specialize (Cenv (lo, hi) Hin). cbn [fst snd] in Cenv.
      unfold in_rg_const in Cenv. rewrite existsb_l_eq in Cenv. apply existsb_exists in Cenv as (R0 & HR0 & Hc0). cbn [Sp np_rest s_rgs] in HR0.
      destruct (is_const (rg_base R0)) as [b0|] eqn:Eb0; [|discriminate]. destruct (is_const (rg_size R0)) as [z0|] eqn:Ez0; [|discriminate].
      destruct (Z.leb b0 lo) eqn:C1; [|discriminate]. apply Z.leb_le in C1, Hc0.
      exists R0. split; [right; exact HR0|]. unfold uE, rsz. rewrite (is_const_u E _ _ Eb0), (is_const_u E _ _ Ez0). clear - C1 Hc0 Hx. lia. }
    destruct He as [He|[He|[He|[He|[He|[He|[He|[He|[He|[He|[He|[He|He]]]]]]]]]]]].
    - exists Rro0. split; [left; reflexivity|]. unfold Rro0, uE, rsz. cbn [rg_base rg_size]. rewrite !lden_lconst, !u_small64 by (unfold two64; clear - Hzro; lia). clear - He Hzro. lia.
    - exact (Hnum 904176 904248 ltac:(cbn; auto 10) He).
    - exact (Hnum 912208 912216 ltac:(cbn; auto 10) He).
    - exact (Hnum 923512 923537 ltac:(cbn; auto 10) He).
    - exact (Hnum 935452 935464 ltac:(cbn; auto 10) He).
    - exact (Hnum 937400 937408 ltac:(cbn; auto 10) He).
    - exact (Hnum 940704 940728 ltac:(cbn; auto 10) He).
    - exact (Hnum 1525856 1525864 ltac:(cbn; auto 10) He).
    - exact (Hnum 1534328 1534336 ltac:(cbn; auto 10) He).
    - exact (Hnum 1534444 1534445 ltac:(cbn; auto 10) He).
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
  set (M2 := with_own M (sm_own M ++ [(rbg, lconst 262144)])) in *.
  set (L1p := fix_post L1 rbg) in *.
  change (fix_post (mrg L1 Sp) rbg) with (mrg L1p Sp) in HDc1.
  rewrite Eu1 in HDc1.
  set (H2 := Hof E1 M2 model2) in *. set (msr2 := restrict H2 ms2) in *.
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ HDr1)) as Hdr10.
  assert (Hpc1 : ms_pc_val ms1 = Z_to_bv 64 0x73c44) by (destruct Hdr10 as (X & _); exact X).
  assert (Ead : lden E1 rbg = wa RBv).
  { rewrite <- (Z_to_bv_bv_unsigned _ (lden E1 rbg)). fold (uE E1 rbg). rewrite Eu1. reflexivity. }
  pose proof (fresh_restrict H2 ms1 false (lden E1 rbg) (Z_to_bv 64 262144) 0x73c44 Hpc1) as FR2.
  rewrite <- Hms2 in FR2. fold msr2 in FR2. rewrite Ead, Hrr1 in FR2.
  set (mB0' := ms_mem msr2) in *.
  assert (EmB0 : mB0' = mrestrict H2 (fresh_mem false (ms_mem ms1) (wa RBv) (Z_to_bv 64 262144))) by (unfold mB0'; rewrite FR2; reflexivity).
  assert (Ereg2 : ms_regs ms2 = rupd R1 a0r (wa RBv)) by (change (ms_regs ms2) with (ms_regs msr2); rewrite FR2; reflexivity).
  assert (Epc2 : ms_pc_val ms2 = wa 0x73c48) by (change (ms_pc_val ms2) with (ms_pc_val msr2); rewrite FR2; reflexivity).
  (* [comment removed for export] *)
  assert (Hlf3 : length front = 3%nat).
  { assert (A1' : (length front <= 3)%nat) by (unfold front; rewrite length_firstn; apply Nat.le_min_l).
    assert (A2' : (2 < length front)%nat) by (apply nth_error_Some; rewrite Pst; discriminate). clear - A1' A2'. lia. }
  pose proof (list3_eq front _ _ _ Hlf3 Pw Pro Pst) as Efront.
  set (FRl := [RG (laddc SPl (-2048)) (lconst 2048) RW TEmpty; Rro0; RG (laddc (p_tg a) 2872) (lconst 16) RW TEmpty]).
  assert (EfrH : forall q0 K0, s_rgs (hand_post Lg q0 K0 [0%nat; 2%nat]) = FRl).
  { intros q0 K0. unfold hand_post. cbn [s_rgs Lg np_front_f]. rewrite Efront. reflexivity. }
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
  assert (HcB : forall x, gCELLS_B CA c SB SP TP K TSDA PT TT x -> COV x /\ ~ (RBv <= x < RBv + 262144) /\ ~ (FAv <= x < FAv + 262144)).
  { intros x Hx. unfold gCELLS_B in Hx. cbv zeta in Hx. fold SHv SHFv in Hx. rewrite ESHv, ESHFv in Hx.
    destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]]].
    - split; [right; left; exact Hx|]. unfold RBv, FAv. clear - Hx B0 BP Hcr HSPr. lia.
    - split; [right; right; right; left; clear - Hx; lia|]. unfold RBv, FAv. clear - Hx T1 B0 Hcr. lia.
    - split; [right; right; right; right; left; clear - Hx Hcr; lia|]. unfold RBv, FAv. clear - Hx B0 Hcr. lia.
    - split; [right; right; left; exact Hx|]. unfold RBv, FAv. clear - Hx Hdisj B0 Hcr. unfold PG_SIZE in Hdisj. fold TT in Hdisj. lia.
    - split; [right; right; right; right; right; left; exact Hx|]. unfold RBv, FAv. clear - Hx S1 B0 Hcr. lia.
    - split; [right; right; right; right; right; right; exact Hx|]. unfold RBv, FAv. clear - Hx S1 B0 Hcr. lia.
    - split; [left; exact (HENVrg x Hx)|]. pose proof (HENV x Hx) as Hn. unfold gCHC in Hn. cbv zeta in Hn. unfold RBv, FAv. clear - Hn. lia. }
  assert (HB0 : agree_on (gCELLS_B CA c SB SP TP K TSDA PT TT) mB0' (gmB0 mA c SB)).
  { intros x Hx Hcl. destruct (HcB x Hcl) as (Hc & Hn1 & _). unfold gmB0. rewrite kz_out by (first [exact Hx | exact Hn1]). exact (HmB0 x Hx Hc Hn1). }
  (* [comment removed for export] *)
  destruct A2 as (A2_10 & A2_11 & A2_12 & A2_13 & A2_14 & A2_15 & A2_17).
  assert (QB1 : getr (ms_regs ms2) (1%bv : reg) = wa 481796).
  { replace (1%bv : reg) with (Z_to_bv 5 1) by (apply bv_eq; reflexivity). rewrite Ereg2, getr_rupd_other by regne. exact A3. }
  assert (QB2 : getr (ms_regs ms2) (2%bv : reg) = wa (SP - 400)).
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
  assert (QB22 : getr (ms_regs ms2) (22%bv : reg) = wa 923480).
  { replace (22%bv : reg) with (Z_to_bv 5 22) by (apply bv_eq; reflexivity). rewrite Ereg2, getr_rupd_other by regne. exact A7. }
  assert (HCT : CA = TT + 208) by (clear - B0; lia).
  assert (HK : 0 <= K <= 1023) by (clear - CT1 CT2; lia).
  assert (Hvals : 0 <= st < 2^64 /\ 0 <= st2 < 2^64 /\ 0 <= mm1 < 2^64 /\ 0 <= mm2 < 2^64) by (clear - Hst Hst2 Hmm1 Hmm2; lia).
  assert (Iwsh' : wr mr SHv 32768) by (rewrite ESHv; exact Iwsh).
  assert (Iwshf' : wr mr SHFv 32768) by (rewrite ESHFv; exact Iwshf).
  destruct (@gstageB (mkFP (ms_fregs ms2) (ms_fcsr ms2)) (ms_rom ms2) mr mA regs CA ND c SB SP st st2 TP K TSDA PT TT mm1 mm2
              Hcls HND1 HSPp HSTK HCA' HCT HSB' HSEP' HO HK Hvals HENV HSHs Ist2 Iwc Iri Iwri Imm1 Imm2 Iwt Iwsh'
              FW6 FW0 FW1 FW2 FW3 FW4 FW7 FW8 FW9 FW10 FW11 FW12 FW13 FW14 FW15 FW16 FW17 FW18 Itls2 Itls3 Itls4 Itls5 A9
              mB0' HB0 (ms_regs ms2) QB1 QB2 QB4 QB8 QB10 QB21 QB22)
    as (RB2 & mB & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & HPB & HFB).
  (* [comment removed for export] *)
  assert (Hn33g : (n0 <= s_next (hand_post Lg 0x73c44 K34 [0%nat; 2%nat]))%positive) by (cbn [hand_post Lg np_front_f s_next]; clear; lia).
  assert (Hn33 : (s_next S <= s_next (hand_post Lg 0x73c44 K34 [0%nat; 2%nat]))%positive) by (cbn [hand_post Lg np_front_f s_next]; unfold n0; clear; lia).
  assert (HwL1p : state_wf L1p = true).
  { unfold L1p. apply fix_post_wf.
    - unfold L1, ecall_tpl. apply with_regs_wf; [exact (hand_post_wf Lg _ _ _ CwLg)|].
      repeat (constructor; [split; [intros Hc0; vm_compute in Hc0; discriminate | cbn [fst snd]; first [exact (lwf_mono' _ _ _ Hn33g Hwrb) | apply lwf_lconst]] |]). constructor.
    - unfold L1, ecall_tpl. rewrite with_regs_next. exact (lwf_mono' _ _ _ Hn33g Hwrb). }
  assert (Pw2 : nth_error (s_rgs L1p) 0 = Some (RG (laddc SPl (-2048)) (lconst 2048) RW TEmpty)) by (rewrite Efr1; reflexivity).
  assert (Pst2 : nth_error (s_rgs L1p) 2 = Some (RG (laddc (p_tg a) 2872) (lconst 16) RW TEmpty)) by (rewrite Efr1; reflexivity).
  assert (Esp1 : uE E1 SPl = SP) by exact (uE_agree (s_next S) E E1 _ HwSP Ha1).
  assert (Est1 : uE E1 (laddc (p_tg a) 2872) = TT + 2872) by (rewrite (uE_agree (s_next S) E E1 _ (lwf_laddc _ _ _ HwTG) Ha1); exact Est).
  set (OWN_B := fun x : Z => SHv <= x < SHv + 32768 \/ RIv + 48 <= x < RIv + 56 \/ CA + 2584 <= x < CA + 2592).
  assert (HBsp : 2048 <= uE E1 SPl <= 2^47) by (rewrite Esp1; clear - HSPr; lia).
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
  assert (HBfr : forall x, 0 <= x < 2^64 -> ~ (uE E1 SPl - 2048 <= x < uE E1 SPl) ->
            ~ (uE E1 (laddc (p_tg a) 2872) <= x < uE E1 (laddc (p_tg a) 2872) + 16) -> ~ OWN_B x -> mB (wa x) = mB0' (wa x)).
  { intros x Hx Hw Hs HO1. rewrite Esp1 in Hw. rewrite Est1 in Hs. destruct HFB as [HFB1 _]. apply (HFB1 x Hx).
    - clear - Hw. lia.
    - intros Hc0. apply HO1. left. exact Hc0.
    - intros Hc0. apply HO1. right. left. exact Hc0.
    - intros Hc0. apply HO1. right. right. exact Hc0.
    - clear - Hs. lia. }
  rewrite <- Epc2 in B1.
  apply (den_run_app_x cfg LIMIT model0 Hwx _ L1p Sp E1 M2 ms2 model2 T SPl (laddc (p_tg a) 2872) 0%nat 2%nat TEmpty TEmpty 0x73c44 K34
           [3; 4]%nat RB2 mB OWN_B 2048 ltac:(lia) HDc1 HwL1p eq_refl Pw2 Pst2 HBsp HBst k34_cases B1 HBkeep HBown HBfr (proj2 HFB)).
  intros E2 ms3 model3 HD3 Ha3 Hfz3 Hrr3 Hvis3 HH3 Hrm3.
  (* [comment removed for export] *)
  set (Lh2 := hand_post L1p 0x73c44 K34 [0%nat; 2%nat]) in *.
  set (L2 := ecall_tpl L1p [0%nat; 2%nat] fag) in *.
  assert (HwfM2 : sm_wf (s_next L1p) M2 = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ HDc1).
  assert (Hn1p : (s_next S <= s_next L1p)%positive) by (unfold L1p, fix_post; cbn [s_next]; unfold L1, ecall_tpl; rewrite with_regs_next; exact Hn33).
  assert (Hn1pg : (n0 <= s_next L1p)%positive) by (unfold L1p, fix_post; cbn [s_next]; unfold L1, ecall_tpl; rewrite with_regs_next; exact Hn33g).
  assert (Ha13g : agree n0 E E2).
  { apply (agree_trans _ E E1 E2); [exact Ha1g|]. exact (agree_mono _ (s_next L1p) _ _ Hn1pg Ha3). }
  assert (Ha13 : agree (s_next S) E E2) by (apply (agree_mono _ n0); [unfold n0; clear; lia | exact Ha13g]).
  assert (Hagr2g : forall E'', agree (s_next (mrg Lh2 Sp)) E2 E'' -> agree n0 E E'').
  { intros E'' Ha''. apply (agree_trans _ E E2 E''); [exact Ha13g|].
    apply (agree_mono _ (s_next (mrg Lh2 Sp))); [cbn [mrg Lh2 hand_post s_next]; clear - Hn1pg; lia | exact Ha'']. }
  assert (Hagr2 : forall E'', agree (s_next (mrg Lh2 Sp)) E2 E'' -> agree (s_next S) E E'').
  { intros E'' Ha''. apply (agree_mono _ n0); [unfold n0; clear; lia | exact (Hagr2g E'' Ha'')]. }
  assert (Efa : uE E fag = FAv).
  { unfold fag. rewrite uE_laddc_z by (rewrite Erb; unfold RBv, two64; clear - B0 Hcr; lia). rewrite Erb. reflexivity. }
  assert (Hwfa : lwf n0 fag = true) by (unfold fag; apply lwf_laddc; exact Hwrb).
  assert (HDr2 : DEN ASEGS LIMIT model0 (ms_mem ms3) E2 (mrg L2 Sp) M2 ms3 model3).
  { change (mrg L2 Sp) with (with_regs_t (mrg Lh2 Sp) (s_regs L2)).
    apply den_regs_eq; [exact HD3|]. intros E'' Ha'' r.
    pose proof (dn_sden _ _ _ _ _ _ _ _ _ HD3 E'' Ha'') as (_ & _ & _ & Hregs & _).
    rewrite <- (Hregs r). cbn [restrict ms_regs]. rewrite Hrr3.
    unfold L2, ecall_tpl. fold Lh2. apply (with_regs_den E'' RB2).
    - intros r'. pose proof (Hregs r') as X. cbn [restrict ms_regs mrg s_regs] in X. rewrite Hrr3 in X. symmetry. exact X.
    - destruct B2 as (Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q17).
      assert (Hlfa : lden E'' fag = wa FAv).
      { rewrite (lden_agree_wf n0 E E'' fag Hwfa (Hagr2g E'' Ha'')).
        rewrite <- (Z_to_bv_bv_unsigned _ (lden E fag)). fold (uE E fag). rewrite Efa. reflexivity. }
      repeat (constructor; [split; [intros Hc0; vm_compute in Hc0; discriminate | cbn [fst snd]; rewrite ?lden_lconst; first [rewrite Hlfa; symmetry; exact Q10 | symmetry; assumption]] |]).
      constructor. }
  (* [comment removed for export] *)
  assert (Eu2 : uE E2 fag = FAv) by (rewrite (uE_agree n0 E E2 _ Hwfa Ha13g); exact Efa).
  assert (Efr2 : s_rgs L2 = FRl) by (unfold L2, ecall_tpl; rewrite with_regs_rgs; unfold hand_post; cbn [s_rgs]; rewrite Efr1; reflexivity).
  assert (Hsh2 : shape (s_rgs (mrg L2 Sp)) = shape (s_rgs (mrg L Sp))).
  { cbn [mrg s_rgs]. rewrite Efr2. cbn [L np_front s_rgs]. rewrite Efront. reflexivity. }
  assert (Hout2 : forall x, outside E (s_rgs (mrg L Sp)) (wa x) -> outside E2 (s_rgs (mrg L2 Sp)) (wa x)).
  { intros x Hx. apply (outside_shape E2 (s_rgs (mrg L Sp))); [exact Hsh2|]. exact (proj1 (outside_agree (s_next L) E E2 _ _ HbwS Ha13) Hx). }
  assert (Hc2nr : forall fl, arg (mrg L2 Sp) 3 = Some fl -> mmap_noreserve_b (Z_to_bv 64 fl) = false).
  { intros fl Hfl. assert (Efl : fl = 50) by (vm_compute in Hfl; injection Hfl as <-; reflexivity). rewrite Efl. reflexivity. }
  assert (Hc2top : uE E2 fag + 262144 <= 2^47) by (rewrite Eu2; unfold FAv; clear - B0 Hcr; lia).
  assert (Hc2rg : forall R0, In R0 (s_rgs (mrg L2 Sp)) -> forall w, uE E2 (rg_base R0) <= w < uE E2 (rg_base R0) + rsz E2 R0 ->
            ~ (uE E2 fag <= w < uE E2 fag + 262144)).
  { intros R0 HR0 w Hw Hc0. rewrite Eu2 in Hc0.
    pose proof (Hout2 w (Hvout w ltac:(clear - Hc0; lia))) as Hou. unfold outside in Hou. rewrite Forall_forall in Hou. specialize (Hou R0 HR0).
    rewrite u_wa_small in Hou by (unfold FAv in Hc0; clear - Hc0 B0 Hcr; lia). unfold uE in Hw. clear - Hou Hw Hc0. lia. }
  assert (Hc2own : forall w, own_pt E2 M2 w -> ~ (uE E2 fag <= bv_unsigned (Z_to_bv 64 w) < uE E2 fag + 262144)).
  { intros w Hw Hc0. rewrite Eu2 in Hc0.
    destruct (proj1 (own_pt_agree (s_next L1p) E1 E2 M2 w HwfM2 Ha3) Hw) as (p & Hp & Hpw).
    cbn [M2 with_own sm_own] in Hp. apply in_app_or in Hp as [Hp|[<-|[]]].
    - assert (Hw0 : own_pt E M w) by exact (proj1 (own_pt_agree (s_next L) E E1 M w HwfM Ha1) (ex_intro _ p (conj Hp Hpw))).
      rewrite u_small64 in Hc0 by exact (Hw64 w Hw0).
      destruct (virgin_not_own LIMIT model0 mem0 E S M ms model a Hd HA0 Hne Hown_eq c Hcin Z0 w Hw0) as [_ N2]. apply N2. exact Hc0.
    - cbn [fst snd] in Hpw. rewrite Eu1, uE_lc in Hpw by (clear; lia).
      rewrite u_small64 in Hc0 by (unfold RBv, two64 in *; clear - Hpw B0 Hcr; lia). unfold RBv, FAv in *. clear - Hpw Hc0. lia. }
  assert (Hc2frz : forall w, frz_pt E2 M2 w -> ~ (uE E2 fag <= w < uE E2 fag + 262144)).
  { intros w Hw Hc0. rewrite Eu2 in Hc0.
    assert (Hw1 : frz_pt E1 M w) by exact (proj1 (frz_pt_agree (s_next L1p) E1 E2 M2 w HwfM2 Ha3) Hw).
    assert (Hw0 : frz_pt E M w) by exact (proj1 (frz_pt_agree (s_next L) E E1 M w HwfM Ha1) Hw1).
    exact (pg_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne w (HinPG w ltac:(right; exact Hc0)) Hw0). }
  apply (den_commit_own cfg LIMIT model0 Hwx Hsegb Hoff Hrespos Hreswf (ms_mem ms3) (mrg L2 Sp) E2 M2 ms3 model3 T fag jP gP HDr2
           eq_refl eq_refl Cfk2 HgP Ege Hc2nr eq_refl Hc2top Hc2rg Hc2own Hc2frz).
  intros ms4 model4 Hms4 HDc2.
  (* [comment removed for export] *)
  set (M4 := with_own M2 (sm_own M2 ++ [(fag, lconst 262144)])) in *.
  set (L2p := fix_post L2 fag) in *.
  change (fix_post (mrg L2 Sp) fag) with (mrg L2p Sp) in HDc2.
  rewrite Eu2 in HDc2.
  set (H4 := Hof E2 M4 model4) in *. set (msr4 := restrict H4 ms4) in *.
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ HDr2)) as Hdr20.
  assert (Hpc3 : ms_pc_val ms3 = Z_to_bv 64 0x73c44) by (destruct Hdr20 as (X & _); exact X).
  assert (Ead2 : lden E2 fag = wa FAv).
  { rewrite <- (Z_to_bv_bv_unsigned _ (lden E2 fag)). fold (uE E2 fag). rewrite Eu2. reflexivity. }
  pose proof (fresh_restrict H4 ms3 false (lden E2 fag) (Z_to_bv 64 262144) 0x73c44 Hpc3) as FR4.
  rewrite <- Hms4 in FR4. fold msr4 in FR4. rewrite Ead2, Hrr3 in FR4.
  set (mC0' := ms_mem msr4) in *.
  assert (EmC0 : mC0' = mrestrict H4 (fresh_mem false (ms_mem ms3) (wa FAv) (Z_to_bv 64 262144))) by (unfold mC0'; rewrite FR4; reflexivity).
  assert (Ereg4 : ms_regs ms4 = rupd RB2 a0r (wa FAv)) by (change (ms_regs ms4) with (ms_regs msr4); rewrite FR4; reflexivity).
  assert (Epc4 : ms_pc_val ms4 = wa 0x73c48) by (change (ms_pc_val ms4) with (ms_pc_val msr4); rewrite FR4; reflexivity).
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
    { refine (proj1 (dn_own _ _ _ _ _ _ _ _ _ HDc2 (fag, lconst 262144) _ x _)).
      - cbn [M4 with_own sm_own]. apply in_or_app. right. left. reflexivity.
      - cbn [fst snd]. rewrite Eu2, uE_lc by (clear; lia). exact Hx. }
    rewrite Hv4. apply fresh_mem_in. change (Z_to_bv 64 262144) with (wa 262144).
    rewrite !u_wa_small by (first [unfold FAv in *; clear - Hx B0 Hcr; lia | clear; lia]). exact Hx. }
  assert (HC0 : agree_on (gCELLS_C CA c SB SP TP K TSDA PT TT) mC0' (kz mB FAv 262144)).
  { intros x Hx [Hcl|Hfa].
    - destruct (HcB x Hcl) as (Hc & _ & Hn2). rewrite kz_out by (first [exact Hx | exact Hn2]). exact (HmC0 x Hx Hc Hn2).
    - rewrite kz_in by (first [exact Hx | exact Hfa]). exact (HmC0fa x Hfa). }
  destruct B2 as (B2_10 & B2_11 & B2_12 & B2_13 & B2_14 & B2_15 & B2_17).
  assert (QC1 : getr (ms_regs ms4) (1%bv : reg) = wa 481796).
  { replace (1%bv : reg) with (Z_to_bv 5 1) by (apply bv_eq; reflexivity). rewrite Ereg4, getr_rupd_other by regne. exact B3. }
  assert (QC2 : getr (ms_regs ms4) (2%bv : reg) = wa (SP - 448)).
  { replace (2%bv : reg) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity). rewrite Ereg4, getr_rupd_other by regne. exact B4. }
  assert (QC4 : getr (ms_regs ms4) (4%bv : reg) = wa TP).
  { replace (4%bv : reg) with (Z_to_bv 5 4) by (apply bv_eq; reflexivity). rewrite Ereg4, getr_rupd_other by regne. exact B8. }
  assert (QC8 : getr (ms_regs ms4) (8%bv : reg) = wa 262144).
  { replace (8%bv : reg) with (Z_to_bv 5 8) by (apply bv_eq; reflexivity). rewrite Ereg4, getr_rupd_other by regne. exact B5. }
  assert (QC10 : getr (ms_regs ms4) (10%bv : reg) = wa FAv).
  { replace (10%bv : reg) with a0r by (apply bv_eq; reflexivity). rewrite Ereg4. apply getr_rupd_same. regne. }
  assert (QC21 : getr (ms_regs ms4) (21%bv : reg) = wa (sz_tbl c)).
  { replace (21%bv : reg) with (Z_to_bv 5 21) by (apply bv_eq; reflexivity). rewrite Ereg4, getr_rupd_other by regne. exact B6. }
  assert (QC22 : getr (ms_regs ms4) (22%bv : reg) = wa 923480).
  { replace (22%bv : reg) with (Z_to_bv 5 22) by (apply bv_eq; reflexivity). rewrite Ereg4, getr_rupd_other by regne. exact B7. }
  destruct (@gstageC (mkFP (ms_fregs ms4) (ms_fcsr ms4)) (ms_rom ms4) mr mA regs CA ND c SB SP st st2 TP K TSDA PT TT mm1 mm2
              Hcls HND1 HSPp HSTK HCA' HCT HSB' HSEP' HO HK Hvals HENV HSHs HSHF Ist Iwc Iri Iwri Iwt Iwshf' RSB RRIB
              FW2 FW3 FW7 FW8 FW9 FW10 FW11 FW12 FW13 FW14 FW15 FW16 FW17 FW18 Itls2 Itls3 Itls4 Itls5 HIMG A9
              mB0' HB0 mB mC0' HPB HFB HC0 (ms_regs ms4) QC1 QC2 QC4 QC8 QC10 QC21 QC22)
    as (R3 & m3 & C1 & C2 & C10 & CK & C34 & HIG & HCfr & HCgr).
  (* [comment removed for export] *)
  assert (Hn66 : (n0 <= s_next (hand_post L1p 0x73c44 K34 [0%nat; 2%nat]))%positive) by (cbn [hand_post s_next]; clear - Hn1pg; lia).
  assert (HwL2p : state_wf L2p = true).
  { unfold L2p. apply fix_post_wf.
    - unfold L2, ecall_tpl. apply with_regs_wf; [exact (hand_post_wf L1p _ _ _ HwL1p)|].
      repeat (constructor; [split; [intros Hc0; vm_compute in Hc0; discriminate | cbn [fst snd]; first [exact (lwf_mono' _ _ _ Hn66 Hwfa) | apply lwf_lconst]] |]). constructor.
    - unfold L2, ecall_tpl. rewrite with_regs_next. exact (lwf_mono' _ _ _ Hn66 Hwfa). }
  assert (Pw4 : nth_error (s_rgs L2p) 0 = Some (RG (laddc SPl (-2048)) (lconst 2048) RW TEmpty)) by (rewrite Efr2p; reflexivity).
  assert (Pst4 : nth_error (s_rgs L2p) 2 = Some (RG (laddc (p_tg a) 2872) (lconst 16) RW TEmpty)) by (rewrite Efr2p; reflexivity).
  assert (Esp2 : uE E2 SPl = SP) by exact (uE_agree (s_next S) E E2 _ HwSP Ha13).
  assert (Est2 : uE E2 (laddc (p_tg a) 2872) = TT + 2872) by (rewrite (uE_agree (s_next S) E E2 _ (lwf_laddc _ _ _ HwTG) Ha13); exact Est).
  set (OWN_C := fun x : Z => FAv <= x < FAv + 262144 \/ SHFv <= x < SHFv + 32768 \/ owned_C CA SB c x).
  assert (HCsp : 2048 <= uE E2 SPl <= 2^47) by (rewrite Esp2; clear - HSPr; lia).
  assert (HCst : uE E2 (laddc (p_tg a) 2872) + 16 <= 2^47) by (rewrite Est2; clear - B0; lia).
  assert (Hvown2 : forall x, VOWN x -> own_pt E2 M4 x /\ outside E2 (s_rgs (mrg L2p Sp)) (wa x) /\ ~ frz_pt E2 M4 x).
  { intros x Hv. destruct (Hvown x Hv) as ((p & Hp & Hpw) & V2 & V3). split; [|split].
    - exists p. split; [exact (Hsub4 p Hp)|].
      pose proof (sm_wf_own _ M HwfM) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw p Hp) as [Hf1 Hf2]. cbn [L np_front s_next] in Hf1, Hf2.
      rewrite (uE_agree (s_next S) E E2 _ Hf1 Ha13), (uE_agree (s_next S) E E2 _ Hf2 Ha13). exact Hpw.
    - exact (Hout2 x V2).
    - intros Hf. apply V3. apply (proj1 (frz_pt_agree (s_next L) E E1 M x HwfM Ha1)).
      exact (proj1 (frz_pt_agree (s_next L1p) E1 E2 M2 x HwfM2 Ha3) Hf). }
  assert (HCown : forall x, 0 <= x < 2^64 -> OWN_C x -> own_pt E2 M4 x /\ outside E2 (s_rgs (mrg L2p Sp)) (wa x) /\ ~ frz_pt E2 M4 x).
  { intros x Hx [HO1|[HO1|HO1]].
    - split; [|split].
      + exists (fag, lconst 262144). split; [cbn [M4 with_own sm_own]; apply in_or_app; right; left; reflexivity|].
        cbn [fst snd]. rewrite Eu2, uE_lc by (clear; lia). exact HO1.
      + exact (Hout2 x (Hvout x ltac:(clear - HO1; lia))).
      + intros Hf. apply (Hc2frz x Hf). rewrite Eu2. exact HO1.
    - apply Hvown2. unfold VOWN. rewrite ESHFv in HO1. right. right. right. exact HO1.
    - apply Hvown2. unfold VOWN. unfold owned_C in HO1. destruct HO1 as [HO1|[HO1|HO1]]; [left; clear - HO1 Hcr; lia | right; left; clear - HO1 Hcr; lia | left; clear - HO1; lia]. }
  assert (HCfr' : forall x, 0 <= x < 2^64 -> ~ (uE E2 SPl - 2048 <= x < uE E2 SPl) ->
            ~ (uE E2 (laddc (p_tg a) 2872) <= x < uE E2 (laddc (p_tg a) 2872) + 16) -> ~ OWN_C x -> m3 (wa x) = mC0' (wa x)).
  { intros x Hx Hw Hs HO1. rewrite Esp2 in Hw. rewrite Est2 in Hs. apply (HCfr x Hx).
    - exact Hw.
    - intros Hc0. apply HO1. right. left. exact Hc0.
    - clear - Hs. lia.
    - intros Hc0. apply HO1. left. exact Hc0.
    - intros Hc0. apply HO1. right. right. exact Hc0. }
  rewrite <- Epc4 in C1.
  apply (den_run_app_x cfg LIMIT model0 Hwx _ L2p Sp E2 M4 ms4 model4 T SPl (laddc (p_tg a) 2872) 0%nat 2%nat TEmpty TEmpty 0x43f08 K34
           [3; 4]%nat R3 m3 OWN_C 2048 ltac:(lia) HDc2 HwL2p eq_refl Pw4 Pst4 HCsp HCst k34_cases C1 C34 HCown HCfr' HCgr).
  intros E3r ms5 model5 HD5r Ha5r Hfz5 Hrr5 Hvis5 HH5 Hrm5.
  (* [comment removed for export] *)
  set (VGC := (n0 + 99)%positive) in *. set (vj0 := (VGC + 1)%positive) in *.
  set (nfin := (vj0 + Pos.of_nat (2 * List.length ccs))%positive) in *.
  set (chl := lscale 8 (lvar VGC)) in *.
  set (TTz := pz_step pz c).
  set (E3 := ext_cls (upd E3r VGC (wa (RBv / 8))) vj0 ccs (fT TTz)).
  assert (Hs_h : s_next (mrg (hand_post L2p 0x43f08 K34 [0%nat; 2%nat]) Sp) = VGC).
  { cbn [mrg hand_post s_next]. unfold L2p, fix_post. cbn [s_next]. unfold L2, ecall_tpl. rewrite with_regs_next. unfold hand_post. cbn [s_next].
    unfold L1p, fix_post. cbn [s_next]. unfold L1, ecall_tpl. rewrite with_regs_next. cbn [hand_post Lg np_front_f s_next]. unfold VGC. clear. lia. }
  assert (Hag3 : agree VGC E3r E3).
  { intros x Hx. unfold E3. rewrite ext_cls_lt by (unfold vj0; clear - Hx; lia). unfold upd.
    replace (Pos.eqb x VGC) with false by (symmetry; apply Pos.eqb_neq; clear - Hx; lia). reflexivity. }
  assert (Evgc : E3 VGC = wa (RBv / 8)).
  { unfold E3. rewrite ext_cls_lt by (unfold vj0; clear; lia). unfold upd. rewrite Pos.eqb_refl. reflexivity. }
  assert (Hcvo : cvals_ok E3 vj0 ccs (fT TTz)) by (unfold E3; apply ext_cls_ok).
  pose proof (den_agree ASEGS LIMIT model0 (ms_mem ms5) E3r E3 _ M4 ms5 model5 HD5r ltac:(rewrite Hs_h; exact Hag3)) as HD5.
  assert (Ha5 : agree (s_next L2p) E2 E3).
  { apply (agree_trans _ E2 E3r E3); [exact Ha5r|]. apply (agree_mono _ VGC); [|exact Hag3]. rewrite <- Hs_h. cbn [mrg hand_post s_next]. clear. lia. }
  (* [comment removed for export] *)
  set (Lh3 := hand_post L2p 0x43f08 K34 [0%nat; 2%nat]) in *.
  set (X := mrg (hand_post Lb 0x43f08 KALLk [0%nat; 2%nat]) Sp) in *.
  assert (En : s_next L2p = s_next Lb).
  { unfold L2p, fix_post. cbn [s_next]. unfold L2, ecall_tpl. rewrite with_regs_next. unfold hand_post. cbn [s_next].
    unfold L1p, fix_post. cbn [s_next]. unfold L1, ecall_tpl. rewrite with_regs_next. cbn [hand_post Lg Lb np_front np_front_f s_next]. clear. lia. }
  assert (Ha35 : agree (s_next S) E E3).
  { apply (agree_trans _ E E2 E3); [exact Ha13|]. apply (agree_mono _ (s_next L2p)); [rewrite En; cbn [Lb np_front s_next]; unfold n0; clear; lia | exact Ha5]. }
  assert (Ha35g : agree n0 E E3).
  { apply (agree_trans _ E E2 E3); [exact Ha13g|]. apply (agree_mono _ (s_next L2p)); [rewrite En; cbn [Lb np_front s_next]; clear; lia | exact Ha5]. }
  assert (Hagr3 : forall E'', agree (s_next (mrg Lh3 Sp)) E3 E'' -> agree (s_next S) E E'').
  { intros E'' Ha''. apply (agree_trans _ E E3 E''); [exact Ha35|].
    apply (agree_mono _ (s_next (mrg Lh3 Sp))); [cbn [mrg Lh3 hand_post s_next]; rewrite En; cbn [Lb np_front s_next]; unfold n0; clear; lia | exact Ha'']. }
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
    unfold X. cbn [s_regs mrg]. unfold hand_post at 1. cbn [s_regs].
      rewrite Ekey. rewrite hregs_get by (first [rewrite SuccNat2Pos.id_succ; clear - Hkk; lia | intros Hc0; apply (f_equal Pos.to_nat) in Hc0; rewrite SuccNat2Pos.id_succ in Hc0; cbn in Hc0; clear - Hc0 Hkk; lia]).
      rewrite <- Ekey.
      destruct (existsb (Pos.eqb (rkey r)) KALLk) eqn:EKa.
      + (* [comment removed for export] *)
        cbn [Lb np_front s_regs].
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
  assert (Efc2p : s_facts L2p = [FRange (lvar (s_next S)) clo chi]).
  { unfold L2p, fix_post. cbn [s_facts]. unfold L2, ecall_tpl. rewrite with_regs_facts. unfold hand_post. cbn [s_facts].
    unfold L1p, fix_post. cbn [s_facts]. unfold L1, ecall_tpl. rewrite with_regs_facts. reflexivity. }
  pose proof (den_facts ASEGS LIMIT model0 (ms_mem ms5) E3 _ M4 ms5 model5 (s_facts X) HDX0) as HDX1.
  assert (HDX1' : DEN ASEGS LIMIT model0 (ms_mem ms5) E3 (with_facts (with_regs_t (mrg Lh3 Sp) (s_regs X)) (s_facts X)) M4 ms5 model5).
  { apply HDX1. intros E'' _ HF''. cbn [with_regs_t mrg s_facts Lh3 hand_post] in HF''. rewrite Efc2p in HF''. cbn [app] in HF''.
    unfold X. cbn [mrg s_facts hand_post Lb np_front app]. exact (Forall_inv_tail HF''). }
  clear HDX0 HDX1. rename HDX1' into HDX0.
  assert (EX : with_facts (with_regs_t (mrg Lh3 Sp) (s_regs X)) (s_facts X) = X).
  { unfold X at 3. unfold with_facts, with_regs_t, mrg, Lh3, hand_post. cbn [s_pc s_regs s_rgs s_facts s_next s_resv].
    rewrite Efr2p, En. cbn [Lb np_front s_rgs s_facts]. rewrite Efront. reflexivity. }
  rewrite EX in HDX0.
  (* [comment removed for export] *)
  assert (HG1 : forall x, 0 <= x < 2^64 -> Hof E M model (wa x) = false -> H2 (wa x) = false -> ~ (RBv <= x < RBv + 262144) -> mB0' (wa x) = mA (wa x)).
  { intros x Hx V0 V2 Hnr. rewrite EmB0. unfold mrestrict. rewrite V2. rewrite fresh_mem_out; [exact (Hvis1 _ V0)|].
    change (Z_to_bv 64 262144) with (wa 262144). rewrite !u_wa_small by (first [exact Hx | unfold RBv; clear - B0 Hcr; lia | clear; lia]). exact Hnr. }
  assert (HG2 : forall x, 0 <= x < 2^64 -> H2 (wa x) = false -> H4 (wa x) = false -> ~ (FAv <= x < FAv + 262144) -> mC0' (wa x) = mB (wa x)).
  { intros x Hx V2 V4 Hnr. rewrite EmC0. unfold mrestrict. rewrite V4. rewrite fresh_mem_out; [exact (Hvis3 _ V2)|].
    change (Z_to_bv 64 262144) with (wa 262144). rewrite !u_wa_small by (first [exact Hx | unfold FAv; clear - B0 Hcr; lia | clear; lia]). exact Hnr. }
  assert (HvisM : forall w, own_pt E M w -> Hof E M model (wa w) = false /\ H2 (wa w) = false /\ H4 (wa w) = false).
  { intros w (p & Hp & Hpw). pose proof (sm_wf_own _ M HwfM) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw p Hp) as [Hf1 Hf2]. cbn [L np_front s_next] in Hf1, Hf2.
    split; [exact (proj1 (dn_own _ _ _ _ _ _ _ _ _ Hd1 p Hp w Hpw))|]. split.
    - refine (proj1 (dn_own _ _ _ _ _ _ _ _ _ HDc1 p (Hsub2 p Hp) w _)). rewrite (uE_agree (s_next S) E E1 _ Hf1 Ha1), (uE_agree (s_next S) E E1 _ Hf2 Ha1). exact Hpw.
    - refine (proj1 (dn_own _ _ _ _ _ _ _ _ _ HDc2 p (Hsub4 p Hp) w _)). rewrite (uE_agree (s_next S) E E2 _ Hf1 Ha13), (uE_agree (s_next S) E E2 _ Hf2 Ha13). exact Hpw. }
  assert (HvisRB : forall x, RBv <= x < RBv + 262144 -> H2 (wa x) = false /\ H4 (wa x) = false).
  { intros x Hx. split.
    - refine (proj1 (dn_own _ _ _ _ _ _ _ _ _ HDc1 (rbg, lconst 262144) _ x _)); [cbn [M2 with_own sm_own]; apply in_or_app; right; left; reflexivity|].
      cbn [fst snd]. rewrite Eu1, uE_lc by (clear; lia). exact Hx.
    - refine (proj1 (dn_own _ _ _ _ _ _ _ _ _ HDc2 (rbg, lconst 262144) _ x _)); [cbn [M4 M2 with_own sm_own]; apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
      cbn [fst snd]. rewrite (uE_agree n0 E E2 _ Hwrb Ha13g), Erb, uE_lc by (clear; lia). exact Hx. }
  (* [comment removed for export] *)
  destruct HFB as [HFB1 HFB2]. fold SHv in HFB1. rewrite ESHv in HFB1. fold SHFv in HCfr. rewrite ESHFv in HCfr. fold RIv in HFB1.
  assert (Hzero5 : forall x, RBv <= x < RBv + 262144 -> ms_mem ms5 (wa x) = Some (Z_to_bv 8 0)).
  { intros x Hx. destruct (HvisRB x Hx) as [V2 V4]. assert (Hx64 : 0 <= x < 2^64) by (unfold RBv in Hx; clear - Hx B0 Hcr; lia).
    rewrite (Hvis5 _ V4). rewrite (HCfr x Hx64).
    2:{ unfold RBv in Hx. clear - Hx B0 BP Hcr HSPr. lia. }
    2:{ unfold RBv in Hx. clear - Hx S1 B0 Hcr. lia. }
    2:{ unfold RBv in Hx. clear - Hx Hdisj B0 Hcr. unfold PG_SIZE in Hdisj. fold TT in Hdisj. lia. }
    2:{ unfold RBv, FAv in *. clear - Hx. lia. }
    2:{ unfold owned_C. unfold RBv in Hx. clear - Hx T1 B0 Hcr. lia. }
    rewrite EmC0. unfold mrestrict. rewrite V4. rewrite fresh_mem_out.
    2:{ change (Z_to_bv 64 262144) with (wa 262144). rewrite !u_wa_small by (first [exact Hx64 | unfold FAv; clear - B0 Hcr; lia | clear; lia]). unfold RBv, FAv in *. clear - Hx. lia. }
    rewrite (Hvis3 _ V2). rewrite (HFB1 x Hx64).
    2:{ unfold RBv in Hx. clear - Hx B0 BP Hcr HSPr. lia. }
    2:{ unfold RBv in Hx. clear - Hx S1 B0 Hcr. lia. }
    2:{ unfold RIv, RBv in *. clear - Hx B0 Hcr. lia. }
    2:{ unfold RBv in Hx. clear - Hx T1 B0 Hcr. lia. }
    2:{ unfold RBv in Hx. clear - Hx Hdisj B0 Hcr. unfold PG_SIZE in Hdisj. fold TT in Hdisj. lia. }
    rewrite EmB0. unfold mrestrict. rewrite V2. apply fresh_mem_in.
    change (Z_to_bv 64 262144) with (wa 262144). rewrite !u_wa_small by (first [exact Hx64 | unfold RBv; clear - B0 Hcr; lia | clear; lia]). exact Hx. }
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
  assert (Hnwin : forall w, outside E (s_rgs (mrg L Sp)) (wa w) -> 0 <= w < 2^64 -> ~ (SP - 2048 <= w < SP) /\ ~ (TT + 2872 <= w < TT + 2888)).
  { intros w Hout Hw. unfold outside in Hout. rewrite Forall_forall in Hout. cbn [mrg s_rgs L np_front] in Hout.
    pose proof (Hout _ (in_or_app _ _ _ (or_introl (nth_error_In _ _ Pw)))) as O1.
    pose proof (Hout _ (in_or_app _ _ _ (or_introl (nth_error_In _ _ Pst)))) as O2.
    cbn [rg_base] in O1, O2. unfold rsz in O1, O2. cbn [rg_size] in O1, O2. rewrite lden_lconst in O1, O2.
    rewrite (u_small64 2048) in O1 by (unfold two64; lia). rewrite (u_small64 16) in O2 by (unfold two64; lia).
    rewrite Ebw in O1. fold (uE E (laddc (p_tg a) 2872)) in O2. rewrite Est in O2. rewrite u_wa_small in O1, O2 by exact Hw. clear - O1 O2. lia. }
  (* [comment removed for export] *)
  assert (Hkeep : forall w, 0 <= w < 2^64 -> own_pt E M w -> outside E (s_rgs (mrg L Sp)) (wa w) -> ~ VOWN w -> ms_mem ms5 (wa w) = mem0 (wa w)).
  { intros w Hw Hm Hout Hnv. destruct (HvisM w Hm) as (V0 & V2 & V4). destruct (Hnwin w Hout Hw) as [Nw Ns].
    destruct (virgin_not_own LIMIT model0 mem0 E S M ms model a Hd HA0 Hne Hown_eq c Hcin Z0 w Hm) as [N1 N2]. fold pz SB in N1, N2. fold RBv in N1. fold FAv in N2.
    rewrite (Hvis5 _ V4). rewrite (HCfr w Hw Nw).
    2:{ intros Hc0. apply Hnv. unfold VOWN. right. right. right. exact Hc0. }
    2:{ exact Ns. }
    2:{ exact N2. }
    2:{ intros Hc0. apply Hnv. unfold VOWN. unfold owned_C in Hc0. clear - Hc0 Hcr. lia. }
    rewrite (HG2 w Hw V2 V4 N2). rewrite (HFB1 w Hw).
    2:{ clear - Nw. lia. }
    2:{ intros Hc0. apply Hnv. unfold VOWN. right. right. left. exact Hc0. }
    2:{ intros Hc0. apply Hnv. unfold VOWN. unfold RIv in Hc0. clear - Hc0 Hcr. lia. }
    2:{ intros Hc0. apply Hnv. unfold VOWN. clear - Hc0. lia. }
    2:{ exact Ns. }
    rewrite (HG1 w Hw V0 V2 N1). rewrite (A11 w Hw Nw).
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
      pose proof (sm_wf_own _ M HwfM) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw p Hp) as [Hf1 Hf2]. cbn [L np_front s_next] in Hf1, Hf2.
      rewrite <- (uE_agree (s_next S) E E2 _ Hf1 Ha13), <- (uE_agree (s_next S) E E2 _ Hf2 Ha13). exact Hpw.
    - right. left. cbn [fst snd] in Hpw. rewrite (uE_agree n0 E E2 _ Hwrb Ha13g), Erb, uE_lc in Hpw by (clear; lia). exact Hpw.
    - right. right. cbn [fst snd] in Hpw. rewrite Eu2, uE_lc in Hpw by (clear; lia). exact Hpw. }
  assert (HshX : shape (s_rgs X) = shape (s_rgs (mrg L Sp))).
  { unfold X. cbn [mrg s_rgs]. unfold hand_post. cbn [s_rgs]. unfold shape. rewrite !map_app. f_equal.
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
    - refine (proj1 (dn_own _ _ _ _ _ _ _ _ _ HDc2 (fag, lconst 262144) _ x _)); [cbn [M4 with_own sm_own]; apply in_or_app; right; left; reflexivity|].
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
    2:{ clear - Hx S3 HSPr Hcr. lia. }
    2:{ clear - Hx. lia. }
    2:{ clear - Hx Hnsh S1 S3 Hcr. lia. }
    2:{ unfold FAv. clear - Hx S1 B0 Hcr. lia. }
    2:{ unfold owned_C. clear - Hx S1 S3 B0 Hcr Hnsh. lia. }
    rewrite (HG2 x Hx64 (Hcov2 x ltac:(right; right; right; exact Hv)) (Hcov4 x ltac:(right; right; right; exact Hv)) ltac:(unfold FAv; clear - Hx S1 B0 Hcr; lia)).
    exact (PBsh x Hx). }
  (* [comment removed for export] *)
  assert (Esh : uE E (p_sh a) = SH) by (symmetry; apply zn_pden).
  set (SHs := SH + 536870912 * c) in *.
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ HD6)) as (_ & _ & _ & _ & _ & _ & HF6 & _).
  assert (Hnewout : forall x, fuc CA SB SH c x -> outside E3 l'' (wa x)).
  { intros x Hx. apply (uncarve_outside E3 X _ 2 stk l'' _ HF6 CpX Hsteps). apply (outside_shape E3 (s_rgs (mrg L Sp))); [exact HshX|].
    exact (proj1 (outside_agree (s_next L) E E3 _ _ HbwS Ha35) (Hvout x Hx)). }
  assert (HwPG : lwf (s_next S) (p_pg a) = true) by exact (lwf_p_nth _ a 3 Hwpri).
  assert (Epg3 : uE E3 (p_pg a) = z_pg pz) by (rewrite (uE_agree (s_next S) E E3 (p_pg a) HwPG Ha35); exact Epg).
  assert (Hcovpg : forall x, z_pg pz <= x < z_pg pz + PG_SIZE -> covered (vm_maps (m_vmmaps model5)) x = true).
  { intros x Hx. apply (grant_covered E3 _ M4 model5 (p_pg a, lconst PG_SIZE, kp) (dn_maps _ _ _ _ _ _ _ _ _ HD6) (dn_gsh _ _ _ _ _ _ _ _ _ HD6) Hgp (is_mark_csize _ _ _)).
    cbn [fst snd]. unfold gsz. cbn [fst snd]. fold (uE E3 (lconst PG_SIZE)). rewrite Epg3, uE_lc by (unfold PG_SIZE; clear; lia). exact Hx. }
  assert (Hcpt : forall x, RBv <= x < RBv + sz_tbl c ->
            own_pt E3 M4 x /\ outside E3 l'' (wa x) /\ ms_mem ms5 (wa x) = Some (Z_to_bv 8 0) /\ app_pt model5 x /\ x < alloc_top (m_vmmaps model5)).
  { intros x Hx. assert (Hxr : RBv <= x < RBv + 262144) by (clear - Hx Hszp; lia).
    assert (Hxf : fuc CA SB SH c x) by (unfold fuc; unfold RBv in Hxr; clear - Hxr; lia).
    assert (Hcov : covered (vm_maps (m_vmmaps model5)) x = true) by exact (Hcovpg x (HinPG x (or_introl Hxr))).
    split; [|split; [exact (Hnewout x Hxf)|split; [exact (Hzero5 x Hxr)|]]].
    - exists (rbg, lconst 262144). split; [cbn [M4 M2 with_own sm_own]; apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
      cbn [fst snd]. rewrite (uE_agree n0 E E3 _ Hwrb Ha35g), Erb, uE_lc by (clear; lia). exact Hxr.
    - split; [|exact (covered_below_top ASEGS LIMIT model0 hyb E3 _ M4 ms5 model5 x HD6 Hcov)].
      split; [left; unfold covered in *; rewrite existsb_app; rewrite Hcov; apply orb_true_r|]. split.
      + unfold in_shadow, SH_LO, SH_HI. apply andb_false_iff. right. apply Z.ltb_ge. unfold RBv in Hxr. clear - Hxr B0 Hcr. lia.
      + unfold RBv in Hxr. clear - Hxr B0 Hcr. lia. }
  assert (Hspt : forall x, SHs <= x < SHs + sz_tbl c / 8 ->
            own_pt E3 M4 x /\ outside E3 l'' (wa x) /\ ms_mem ms5 (wa x) = Some (Z_to_bv 8 250) /\
            in_shadow x = true /\ covered (vm_maps (m_vmmaps model5)) x = true /\ 0 <= x < 2^47).
  { intros x Hx. assert (Hxr : SHs <= x < SHs + 32768) by (clear - Hx Hsz8; lia).
    assert (Hv : VOWN x) by (unfold VOWN; right; right; left; exact Hxr).
    assert (Hxf : fuc CA SB SH c x) by (unfold fuc; unfold SHs in Hxr; clear - Hxr; lia).
    assert (Hzr : in_zr (sm_zr M) x = true).
    { apply (po_zr _ _ _ _ HP0). exists c. split; [exact Hcin|]. left. fold pz. fold SH. exact Hxr. }
    split; [|split; [exact (Hnewout x Hxf)|split; [rewrite (Hvis5 _ (Hv4f x Hxf)); exact (Hfa3 x Hxr)|]]].
    - destruct (Hvown x Hv) as ((p & Hp & Hpw) & _). exists p. split; [exact (Hsub4 p Hp)|].
      pose proof (sm_wf_own _ M HwfM) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw p Hp) as [Hf1 Hf2]. cbn [L np_front s_next] in Hf1, Hf2.
      rewrite (uE_agree (s_next S) E E3 _ Hf1 Ha35), (uE_agree (s_next S) E E3 _ Hf2 Ha35). exact Hpw.
    - split; [exact (dn_zrsh _ _ _ _ _ _ _ _ _ HD6 x Hzr)|]. split; [exact (dn_zrm _ _ _ _ _ _ _ _ _ HD6 x Hzr)|]. unfold SHs in Hxr. clear - Hxr S1 S3 Hcr. lia. }
  (* [comment removed for export] *)
  destruct (cls_jb pz mem0 HI c Hcin) as (K0 & K1 & K2 & _).
  assert (Hjn : z_j pz c + 1 <= 262144 / sz_tbl c) by (clear - Hjhi Hmc; lia).
  set (CHB := SB + 4294967296 * c + sz_tbl c * z_j pz c) in *.
  set (CHS := SH + 536870912 * c + sz_tbl c / 8 * z_j pz c) in *.
  assert (ECHB : CHB = RBv) by (unfold CHB, RBv; rewrite Hj0; ring).
  assert (ECHS : CHS = SHs) by (unfold CHS, SHs; rewrite Hj0; ring).
  rewrite <- ECHB in Hcpt, Evgc. rewrite <- ECHS in Hspt.
  assert (S2 : CA + 2592 <= SH \/ SH + 17179869184 <= CA - 128) by (clear - G S1; unfold CA, SH in *; lia).
  assert (E8 : 8 * (CHS - SH_OFF) = CHB).
  { unfold CHS, CHB, SH_OFF. destruct G as (_ & _ & _ & _ & _ & Gm8 & Gsh & _). fold SB SH in Gm8, Gsh.
    pose proof (Z.div_mod SB 8 ltac:(clear; lia)) as Ed. rewrite Gm8, Z.add_0_r in Ed. rewrite Gsh. clear - Ed Hs8. lia. }
  assert (HCHB : 0 <= CHB /\ CHB + sz_tbl c <= 2^47 /\ CHB mod 8 = 0).
  { split; [rewrite ECHB; unfold RBv; clear - B0 Hcr; lia|]. split; [rewrite ECHB; unfold RBv; clear - B0 Hcr Hszp; lia|].
    rewrite <- E8. rewrite Z.mul_comm. apply Z_mod_mult. }
  (* [comment removed for export] *)
  assert (End3 : uE E3 ndl = ND).
  { exact (uE_agree (s_next S) E E3 ndl Hwnd Ha35). }
  assert (Hwnd8 : lwf (s_next S) ND8 = true) by exact (ldiv8_wf _ _ _ Hnd8 Hwnd).
  assert (End8 : uE E3 ND8 = uE E ND8).
  { exact (uE_agree (s_next S) E E3 ND8 Hwnd8 Ha35). }
  pose proof (irange_sound E (s_facts S) ND8 HF0) as Rnd8. fold (uE E ND8) in Rnd8.
  assert (End8b : ND = 8 * uE E ND8) by (apply (uE_ldiv8 E ndl ND8 Hnd8); unfold two64; clear - Rnd8 Cnd8; lia).
  set (N8 := uE E ND8) in *.
  assert (HN8 : 1 <= N8 /\ 8 * N8 <= sz_tbl c) by (clear - End8b HND1 HND; lia).
  (* [comment removed for export] *)
  set (Y0 := with_rgs X l'') in *.
  assert (Hny : s_next Y0 = VGC) by (cbn [Y0 with_rgs s_next X mrg hand_post Lb np_front]; unfold VGC; clear; lia).
  assert (Hnf : (VGC < nfin)%positive) by (unfold nfin, vj0; clear; lia).
  pose proof (den_bump ASEGS LIMIT model0 hyb E3 Y0 M4 ms5 model5 nfin HD7 ltac:(rewrite Hny; clear - Hnf; lia)) as HD7b.
  assert (Echl : forall E4, agree nfin E3 E4 -> lden E4 chl = wa CHB).
  { intros E4 Ha4. unfold chl. rewrite lden_lscale, lden_lvar. rewrite <- (Ha4 VGC Hnf), Evgc.
    rewrite u_wa_small by (destruct HCHB as (Bh1 & Bh2 & _); split; [apply Z.div_pos; [exact Bh1 | clear; lia] | apply Z.div_lt_upper_bound; [clear; lia | clear - Bh1 Bh2 Hszp; lia]]).
    unfold wa. f_equal. destruct HCHB as (_ & _ & Bh3). pose proof (Z.div_mod CHB 8 ltac:(clear; lia)) as Ed. rewrite Bh3, Z.add_0_r in Ed. symmetry. exact Ed. }
  assert (Hcha0 : forall E4, agree (s_next (bump Y0 nfin)) E3 E4 -> lden E4 chl = lden E4 (rget (s_regs (bump Y0 nfin)) (rk 10))).
  { intros E4 Ha4. rewrite (Echl E4 Ha4). pose proof (dn_sden _ _ _ _ _ _ _ _ _ HD7b E4 Ha4) as (_ & _ & _ & Hregs & _).
    specialize (Hregs (Z_to_bv 5 10)). cbn [restrict ms_regs] in Hregs. change (rkey (Z_to_bv 5 10)) with (rk 10) in Hregs.
    rewrite <- Hregs, Hrr5, ECHB. symmetry. exact C10. }
  assert (Hrk : rk 10 <> xH) by (intros Hc0; vm_compute in Hc0; discriminate).
  pose proof (den_reg_eq ASEGS LIMIT model0 hyb E3 _ M4 ms5 model5 (rk 10) chl HD7b Hrk Hcha0) as HD7c.
  set (Y1 := with_reg (bump Y0 nfin) (rk 10) chl) in *.
  (* [comment removed for export] *)
  pose proof (iz_len _ _ HI) as Hlenz.
  assert (Hcsr : forall c', In c' ccs -> 1 <= c' <= 30).
  { intros c' Hc'. apply crange_rng in Hc'. clear - Hc' Cclo1 Cchi. lia. }
  assert (HTT : forall k, 0 <= nth k TTz 0 < 2^64).
  { unfold TTz, pz. apply pz_step_nth_rng; [exact Hlen | exact Hcr | fold pz; clear - K0 Hjn Hnw; lia]. }
  assert (Hwsb : lwf (s_next S) (p_sb a) = true) by (apply lwf_p_nth; exact (awf_pri _ a Haw)).
  pose proof (irange_sound E (s_facts S) (p_sb a) HF0) as Rsb. fold (uE E (p_sb a)) in Rsb. rewrite Esb in Rsb.
  assert (Hsz32 : sz_tbl c mod 32 = 0) by exact (sz_tbl_mod32 c Hcr).
  set (newfacts := FRange (lvar VGC) ((fst (irange (s_facts S) (p_sb a)) + 4294967296 * clo) / 8) ((snd (irange (s_facts S) (p_sb a)) + 4294967296 * chi + 262144) / 8) ::
                   FMod (lvar VGC) 2 0 :: FRange (lsub chl (p_sb a)) (4294967296 * clo) (4294967296 * chi + 262144) :: class_facts (s_facts S) a vj0 ccs).
  assert (Hnfacts : forall E4, agree (s_next Y1) E3 E4 -> Forall (fact_ok E4) newfacts).
  { intros E4 Ha4. change (s_next Y1) with nfin in Ha4.
    assert (Ev4 : bv_unsigned (lden E4 (lvar VGC)) = CHB / 8).
    { rewrite lden_lvar, <- (Ha4 VGC Hnf), Evgc. apply u_wa_small. destruct HCHB as (Bh1 & Bh2 & _).
      split; [apply Z.div_pos; [exact Bh1 | clear; lia] | apply Z.div_lt_upper_bound; [clear; lia | clear - Bh1 Bh2 Hszp; lia]]. }
    assert (Hsj : 0 <= sz_tbl c * z_j pz c /\ sz_tbl c * z_j pz c + 32 <= 262144) by (clear - K0 Hszp Hjn Hnm; nia).
    unfold newfacts. constructor; [|constructor; [|constructor]].
    - cbn [fact_ok]. rewrite Ev4. split; apply Z.div_le_mono; try (clear; lia); unfold CHB; clear - Rsb Hclc Hsj; clearbody c clo chi pz;
        destruct Rsb as [RCh RSh]; destruct Hclc as [C1 C2]; destruct Hsj as [J1 J2]; revert RCh RSh C1 C2 J1 J2;
        generalize (sz_tbl c * z_j pz c) (SB) (fst (irange (s_facts S) (p_sb a))) (snd (irange (s_facts S) (p_sb a))); clear; intros; lia.
    - cbn [fact_ok]. rewrite Ev4. destruct HCHB as (_ & _ & Bh3).
      assert (H32 : CHB mod 32 = 0).
      { unfold CHB. pose proof (iz_sb _ _ HI) as (_ & X2). fold pz SB in X2.
        rewrite Z.add_mod by (clear; lia). rewrite (Z.add_mod (SB)) by (clear; lia).
        replace (SB mod 32) with 0 by (symmetry; pose proof (Z.div_mod (SB) 4096 ltac:(clear; lia)) as Ed; rewrite X2, Z.add_0_r in Ed; rewrite Ed;
          replace (4096 * (SB / 4096)) with (128 * (SB / 4096) * 32) by ring; apply Z_mod_mult).
        replace ((4294967296 * c) mod 32) with 0 by (symmetry; replace (4294967296 * c) with (134217728 * c * 32) by ring; apply Z_mod_mult).
        replace ((sz_tbl c * z_j pz c) mod 32) with 0 by (symmetry; rewrite Z.mul_mod by (clear; lia); rewrite Hsz32; reflexivity).
        reflexivity. }
      pose proof (Z.div_mod CHB 32 ltac:(clear; lia)) as Ed. rewrite H32, Z.add_0_r in Ed. rewrite Ed.
      replace (32 * (CHB / 32)) with (CHB / 32 * 4 * 8) by ring. rewrite Z.div_mul by (clear; lia). change (2 ^ 2) with 4. apply Z_mod_mult.
    - cbn [fact_ok]. rewrite lden_lsub, (Echl E4 Ha4).
      assert (Esb4 : lden E4 (p_sb a) = wa (SB)).
      { rewrite (lden_agree_wf (s_next S) E E4 _ Hwsb); [unfold wa; rewrite <- Esb; unfold uE; rewrite Z_to_bv_bv_unsigned; reflexivity|].
        apply (agree_trans _ E E3 E4); [exact Ha35 | apply (agree_mono _ nfin); [unfold nfin, vj0, VGC, n0; clear; lia | exact Ha4]]. }
      rewrite Esb4. rewrite bv_sub_unsigned. unfold wa. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      destruct HCHB as (Bh1 & Bh2 & _).
      rewrite (Z.mod_small CHB) by (unfold two64; clear - Bh1 Bh2 Hszp; lia). rewrite (Z.mod_small (SB)) by (unfold two64; clear - G; lia).
      rewrite Z.mod_small by (unfold CHB, two64; clear - Hsj Hcr; lia). unfold CHB. clear - Hsj Hclc. lia.
    - apply (class_facts_ok ccs E4 (s_facts S) a vj0 TTz); [| exact HTT |].
      + apply (cvals_ok_agree ccs E3 E4 vj0 (fT TTz) nfin Hcvo Ha4). unfold nfin. clear. lia.
      + intros c' Hc'. pose proof (Hcsr c' Hc') as Hcr'. pose proof (cidx_rng c' Hcr') as Hi'.
        pose proof (irange_sound E (s_facts S) (p_j a c') HF0) as Rj'. fold (uE E (p_j a c')) in Rj'.
        assert (Ej' : uE E (p_j a c') = z_j pz c') by (symmetry; apply zn_pden). rewrite Ej' in Rj'.
        change (nth (5 + 2 * cidx c') TTz 0) with (z_j TTz c'). change (nth (6 + 2 * cidx c') TTz 0) with (z_z TTz c'). unfold TTz.
        (* [comment removed for export] *)
        assert (Ej4 : uE E4 (p_j a c') = z_j pz c').
        { rewrite <- Ej'. apply (uE_agree (s_next S) E E4); [apply lwf_p_nth; exact (awf_pri _ a Haw)|].
          apply (agree_trans _ E E3 E4); [exact Ha35 | apply (agree_mono _ nfin); [unfold nfin, vj0, VGC, n0; clear; lia | exact Ha4]]. }
        rewrite Ej4.
        destruct (Z.eq_dec c' c) as [->|Hne'].
        * rewrite (step_j_same pz c Hlenz Hcr), (step_z_same pz c Hlenz Hcr). clear - Rj'. lia.
        * rewrite (step_j_other pz c Hlenz Hcr c' Hcr' Hne'), (step_z_other pz c Hlenz Hcr c' Hcr' Hne').
          destruct (cls_jb pz mem0 HI c' (rng_in_cls c' Hcr')) as (_ & _ & _ & Kz). clear - Rj' Kz. lia. }
  pose proof (den_add_facts ASEGS LIMIT model0 hyb E3 Y1 M4 ms5 model5 newfacts HD7c Hnfacts) as HD8.
  set (Y2 := with_facts Y1 (s_facts Y1 ++ newfacts)) in *.
  (* [comment removed for export] *)
  set (RSh := RG (laddc (lvar VGC) SH_OFF) ND8 RW (tset 1%positive (BK 250) TEmpty)).
  set (RCh := RG chl ndl RZ TEmpty).
  assert (Hny2 : s_next Y2 = nfin) by reflexivity.
  assert (Hrgs2 : s_rgs Y2 = l'') by reflexivity.
  assert (Ech3 : uE E3 chl = CHB).
  { unfold uE. rewrite (Echl E3 (fun x _ => eq_refl)). apply u_wa_small. destruct HCHB as (Bh1 & Bh2 & _). clear - Bh1 Bh2 Hszp. lia. }
  assert (Ecs3 : uE E3 (laddc (lvar VGC) SH_OFF) = CHS).
  { assert (Ev : uE E3 (lvar VGC) = CHB / 8).
    { apply uE_lvar_wa; [exact Evgc|]. destruct HCHB as (Bh1 & Bh2 & _).
      split; [apply Z.div_pos; [exact Bh1 | clear; lia] | apply Z.div_lt_upper_bound; [clear; lia | clear - Bh1 Bh2 Hszp; lia]]. }
    assert (Ed : CHB / 8 = CHS - SH_OFF) by (rewrite <- E8; rewrite Z.mul_comm; apply Z.div_mul; clear; lia).
    rewrite uE_laddc_z by (rewrite Ev, Ed; unfold two64, CHS; clear - G S1 K0 K2 Hcr Hsz8; lia). rewrite Ev, Ed. ring. }
  assert (Er2 : rsz E3 RSh = N8) by (unfold rsz, RSh; cbn [rg_size]; fold (uE E3 ND8); exact End8).
  assert (Er1 : rsz E3 RCh = ND) by (unfold rsz, RCh; cbn [rg_size]; fold (uE E3 ndl); exact End3).
  assert (Hwn : forall l, lwf (s_next S) l = true -> lwf nfin l = true).
  { intros l Hl. apply (lwf_mono' (s_next S)); [unfold nfin, vj0, VGC, n0; clear; lia | exact Hl]. }
  assert (HD9 : DEN ASEGS LIMIT model0 hyb E3 (addo_post Y2 RSh) M4 ms5 model5).
  { apply (den_add_own ASEGS LIMIT model0 hyb E3 Y2 M4 ms5 model5 RSh HD8).
    - rewrite Hny2. apply lwf_laddc. apply lwf_lvar. exact Hnf.
    - rewrite Hny2. exact (Hwn _ Hwnd8).
    - reflexivity.
    - intros p v Hp. unfold RSh in Hp. cbn [rg_cont] in Hp. destruct (Pos.eq_dec 1 p) as [<-|Hnp].
      + rewrite tget_tset_same in Hp. injection Hp as <-. exists 250. reflexivity.
      + rewrite tget_tset_other in Hp by exact Hnp. rewrite tget_empty in Hp. discriminate.
    - rewrite Er2. clear - HN8. lia.
    - rewrite Er2. change (rg_base RSh) with (laddc (lvar VGC) SH_OFF). rewrite Ecs3.
      destruct (Hspt (CHS + sz_tbl c / 8 - 1) ltac:(clear - Hsz8; lia)) as (_ & _ & _ & _ & _ & N6). clear - N6 HN8 Hs8. lia.
    - intros x Hx. rewrite Er2 in Hx. change (rg_base RSh) with (laddc (lvar VGC) SH_OFF) in Hx. rewrite Ecs3 in Hx.
      destruct (Hspt x ltac:(clear - Hx HN8 Hs8; lia)) as (N1 & _ & N3 & _ & N5 & _). split; [exact N1|]. split; [unfold wa in N3; rewrite N3; discriminate|].
      exact (covered_below_top ASEGS LIMIT model0 hyb E3 _ M4 ms5 model5 x HD6 N5).
    - intros p b Hp. unfold RSh in Hp. cbn [rg_cont] in Hp. rewrite Er2. change (rg_base RSh) with (laddc (lvar VGC) SH_OFF). rewrite Ecs3.
      destruct (Pos.eq_dec 1 p) as [<-|Hnp]; [|rewrite tget_tset_other in Hp by exact Hnp; rewrite tget_empty in Hp; discriminate].
      rewrite tget_tset_same in Hp. injection Hp as <-. split; [clear - HN8; lia|].
      destruct (Hspt (CHS + (1 - 1)) ltac:(clear - Hsz8; lia)) as (_ & _ & N3 & _). exact N3.
    - intros R' HR' w Hw Hc0. rewrite Er2 in Hc0. change (rg_base RSh) with (laddc (lvar VGC) SH_OFF) in Hc0. rewrite Ecs3 in Hc0. rewrite Hrgs2 in HR'.
      destruct (Hspt w ltac:(clear - Hc0 HN8 Hs8; lia)) as (_ & N2 & _ & _ & _ & N6). unfold outside in N2. rewrite Forall_forall in N2. specialize (N2 R' HR').
      rewrite u_wa_small in N2 by (clear - N6; lia). unfold uE in Hw. clear - N2 Hw. lia.
    - unfold rl_ok. cbv zeta. rewrite Er2. change (rg_base RSh) with (laddc (lvar VGC) SH_OFF). rewrite Ecs3. split; [clear - HN8; lia|]. right.
      split; [unfold SH_OFF, CHS; clear - S1 K0 Hcr Hsz8; lia|]. split.
      + intros x Hx. apply (Hcpt x). rewrite <- E8. clear - Hx HN8 Hs8. lia.
      + intros w Hw. destruct (Hspt w ltac:(clear - Hw HN8 Hs8; lia)) as (_ & _ & _ & N4 & N5 & _). split; [exact N4 | exact N5]. }
  assert (HD10 : DEN ASEGS LIMIT model0 hyb E3 (addo_post (addo_post Y2 RSh) RCh) M4 ms5 model5).
  { apply (den_add_own_z ASEGS LIMIT model0 hyb E3 (addo_post Y2 RSh) M4 ms5 model5 RCh HD9).
    - cbn [addo_post s_next]. rewrite Hny2. unfold RCh. cbn [rg_base]. unfold chl. apply lwf_lscale. apply lwf_lvar. exact Hnf.
    - cbn [addo_post s_next]. rewrite Hny2. exact (Hwn _ Hwnd).
    - reflexivity.
    - reflexivity.
    - rewrite Er1. clear - HND1. lia.
    - rewrite Er1. change (rg_base RCh) with chl. rewrite Ech3. destruct HCHB as (_ & Bh2 & _). clear - Bh2 HND. lia.
    - intros x Hx. rewrite Er1 in Hx. change (rg_base RCh) with chl in Hx. rewrite Ech3 in Hx.
      destruct (Hcpt x ltac:(clear - Hx HND; lia)) as (N1 & _ & N3 & _ & N5). split; [exact N1|]. split; [exact N3 | exact N5].
    - intros R' HR' w Hw Hc0. rewrite Er1 in Hc0. change (rg_base RCh) with chl in Hc0. rewrite Ech3 in Hc0.
      cbn [addo_post s_rgs] in HR'. destruct HR' as [<-|HR'].
      + rewrite Er2 in Hw. change (rg_base RSh) with (laddc (lvar VGC) SH_OFF) in Hw. rewrite Ecs3 in Hw.
        destruct (Hspt w ltac:(clear - Hw HN8 Hs8; lia)) as (_ & _ & _ & N4 & _). destruct (Hcpt w ltac:(clear - Hc0 HND; lia)) as (_ & _ & _ & Happ & _).
        unfold app_pt in Happ. destruct Happ as (_ & N4' & _). congruence.
      + rewrite Hrgs2 in HR'. destruct (Hcpt w ltac:(clear - Hc0 HND; lia)) as (_ & N2 & _ & Happ & _). unfold app_pt in Happ. destruct Happ as (_ & _ & N6).
        unfold outside in N2. rewrite Forall_forall in N2. specialize (N2 R' HR').
        rewrite u_wa_small in N2 by (clear - N6; lia). unfold uE in Hw. clear - N2 Hw. lia.
    - unfold rl_ok. cbv zeta. rewrite Er1. change (rg_base RCh) with chl. rewrite Ech3. split; [clear - HND1; lia|]. left.
      intros w Hw. destruct (Hcpt w ltac:(clear - Hw HND; lia)) as (_ & _ & _ & N4 & _). exact N4. }
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
      rewrite (Hhyb_in x ltac:(unfold RBv in Hxr; clear - Hxr B0 Hcr; lia) ltac:(unfold fuc; unfold RBv in Hxr; clear - Hxr; lia)). exact (Hzero5 x Hxr).
    - intros x Hx. unfold SHX in Hx. assert (Hxr : SHs <= x < SHs + 32768) by (unfold SHs; clear - Hx Hsz8; lia).
      rewrite (Hhyb_m3 x ltac:(unfold fuc; unfold SHs in Hxr; clear - Hxr; lia)). exact (Hfa3 x Hxr).
    - intros x Hx. unfold SHX in Hx. rewrite (Hhyb_m3 x ltac:(unfold fuc; clear - Hx; lia)), (Hfa3 x Hx). discriminate. }
  (* [comment removed for export] *)
  assert (Hcb_chain : forall x, CA - 128 <= x < CA + 2592 -> ~ owned_C CA SB c x -> hyb (wa x) = mA (wa x)).
  { intros x Hx Hno. assert (Hv : VOWN x) by (unfold VOWN; left; exact Hx).
    assert (Hx64 : 0 <= x < 2^64) by (clear - Hx Bz1 HCA'; lia).
    assert (V0 := Hcov0 x ltac:(right; right; right; exact Hv)). assert (V2 := Hcov2 x ltac:(right; right; right; exact Hv)).
    assert (V4 := Hcov4 x ltac:(right; right; right; exact Hv)).
    rewrite (Hhyb_m3 x ltac:(unfold fuc; clear - Hx; lia)). rewrite (HCfr x Hx64).
    2:{ clear - Hx HCA'. lia. }
    2:{ clear - Hx S1 S3 B0 Hcr Hnsh. lia. }
    2:{ intros Hc0. apply Hno. unfold owned_C. clear - Hc0 Hx B0. lia. }
    2:{ unfold FAv. clear - Hx T1 B0 Hcr. lia. }
    2:{ exact Hno. }
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
    { intros x Hx. unfold icc in Hx. apply Hcb_chain; [clear - Hx Hir; lia|]. unfold owned_C. clear - Hx Hir Hic Hcr T1 B0. lia. }
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
    rewrite (HG2 x Hx64 V2 V4 ltac:(unfold FAv; clear - Hx Hcr; lia)). rewrite (HFB1 x Hx64).
    2:{ clear - Hx HSB'. lia. }
    2:{ clear - Hx S1 S3 B0 Hcr. lia. }
    2:{ intros Hc0. apply Hno. unfold owned_C. unfold RIv in Hc0. clear - Hc0. lia. }
    2:{ clear - Hx T1 B0. lia. }
    2:{ clear - Hx Hdisj B0. unfold PG_SIZE in Hdisj. fold TT in Hdisj. lia. }
    exact (HG1 x Hx64 V0 V2 ltac:(unfold RBv; clear - Hx Hcr; lia)). }
  assert (HF2 : forall x, pri_foot_z pz x -> ~ owned_C CA SB c x -> (forall i, 1 <= i <= 31 -> i <> c -> ~ icc CA i x) ->
            ~ (SH + 536870912 * c <= x < SH + 536870912 * c + 32768) ->
            ~ (SH + 536870912 * c + 469762048 <= x < SH + 536870912 * c + 469762048 + 32768) -> hyb (wa x) = mem0 (wa x)).
  { intros x Hf Hno Hni Hn5 Hn6. pose proof (pri_foot_rng E a mem0 HI x Hf) as Rx.
    assert (Hx64 : 0 <= x < 2^64) by (clear - Rx; lia).
    destruct (fuc_b CA SB SH c x) eqn:Eb; [apply fuc_b_spec in Eb | apply (Hhyb_out x Hx64); intros Hc0; apply fuc_b_spec in Hc0; congruence].
    destruct (foot_not_virgin pz mem0 c HI Hdisj Hcin Z0 x Hf) as [Nrb Nfa]. fold SB in Nrb, Nfa.
    assert (HA11 : mA (wa x) = mr (wa x)).
    { apply (A11 x Hx64).
      - unfold fuc in Eb. clear - Eb Nrb Nfa Hn5 Hn6 HCA' HSB'. lia.
      - intros i Hi Hc0. destruct (Z.eq_dec i c) as [->|Hic]; [apply Hno; unfold owned_C; clear - Hc0; lia | exact (Hni i Hi Hic Hc0)].
      - intros Hc0. apply Hno. unfold owned_C. unfold RIv in Hc0. clear - Hc0. lia. }
    destruct Eb as [Eb|[Eb|Eb]].
    - rewrite (Hcb_chain x Eb Hno), HA11. apply Hmr_foot. left. exact Eb.
    - rewrite (Hri_chain x Eb Hno), HA11. apply Hmr_foot. right. left. exact Eb.
    - exfalso. clear - Eb Nrb Nfa Hn5 Hn6. lia. }
  assert (Hjb' : z_j pz c + 1 + mc_tbl c / 2 <= 262144 / sz_tbl c) by (clear - Hjhi; lia).
  pose proof (INV_Az_step2 pz mem0 hyb c HI Hdisj Hcin Hjb' HIo' HPo' HST' HWC' HICv HF2) as HIz'.
  (* [comment removed for export] *)
  set (pri' := set_classes vj0 ccs (a_pri a)) in *.
  set (aw := a_with a pri').
  assert (Epz' : pden E3 a = pz) by exact (pden_agree (s_next S) E E3 a Haw Ha35).
  assert (Epz2 : pden E3 aw = TTz).
  { unfold pden. change (a_pri aw) with pri'. unfold pri'. rewrite (map_set_classes ccs E3 vj0 (a_pri a) TTz Hcvo HTT).
    fold (pden E3 a). rewrite Epz'. exact (setz_step ccs pz c Hlenz Hcsr Hccs). }
  assert (Hne' : pri' <> []).
  { intros Hn. pose proof (f_equal (@List.length lin) Hn) as XL. unfold pri' in XL. rewrite set_classes_length, Hlen in XL. discriminate. }
  assert (Hbase : forall k, (k < 5)%nat -> nth k pri' lc0 = nth k (a_pri a) lc0).
  { intros k Hk5. unfold pri'. exact (set_classes_base ccs vj0 (a_pri a) k Hk5 Hcsr Hlen). }
  assert (Hmono : forall x, pri_foot_z (pden E a) x -> pri_foot_z (pden E3 (a_with a pri')) x).
  { intros x Hf. change (a_with a pri') with aw. rewrite Epz2. fold pz in Hf. unfold TTz, pri_foot_z in *.
    rewrite (step_ca pz c Hlenz Hcr), (step_sb pz c Hlenz Hcr), (step_sh pz c Hlenz Hcr).
    destruct Hf as [Hf|[Hf|[Hf|(c' & Hc' & Hf)]]]; [left; exact Hf | right; left; exact Hf | right; right; left; exact Hf |]. right. right. right. exists c'. split; [exact Hc'|].
    destruct (Z.eq_dec c' c) as [->|Hnc]; [rewrite (step_z_same pz c Hlenz Hcr); rewrite Z0 in Hf; clear - Hf; lia|].
    rewrite (step_z_other pz c Hlenz Hcr c' (in_cls_rng c' Hc') Hnc). exact Hf. }
  assert (Hdepf : forall x, 0 <= x < 2^64 -> downed (dD1 E a) (dB1 E a) x -> hyb (wa x) = mem0 (wa x)).
  { intros x Hx Hdw. apply (Hhyb_out x Hx). intros Hn. destruct (Hfuc_v x Hn) as [Hv|Hv].
    - assert (F1 : pri_foot_z pz x).
      { unfold pri_foot_z. fold CA SB SH. unfold VOWN in Hv. destruct Hv as [Hv|[Hv|Hv]]; [left; exact Hv | right; left; exact Hv |].
        right. right. right. exists c. split; [exact Hcin|]. right. right. exact Hv. }
      exact (pri_not_downed LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1 Hdw).
    - pose proof (ha_own _ _ _ _ HA0 x Hx Hdw) as Hod.
      destruct (virgin_not_own LIMIT model0 mem0 E S M ms model a Hd HA0 Hne Hown_eq c Hcin Z0 x Hod) as [N1 N2]. fold pz SB in N1, N2. fold RBv in N1. fold FAv in N2.
      clear - Hv N1 N2. tauto. }
  assert (Hjmono : forall c', In c' CLS -> z_j pz c' <= z_j TTz c').
  { intros c' Hc'. unfold TTz. destruct (Z.eq_dec c' c) as [->|Hnc]; [rewrite (step_j_same pz c Hlenz Hcr); clear; lia|].
    rewrite (step_j_other pz c Hlenz Hcr c' (in_cls_rng c' Hc') Hnc). clear. lia. }
  assert (Hext_step : forall b z, ext_sem (pden E a) b z -> ext_sem (pden E3 (a_with a pri')) b z).
  { intros b z Hbz. change (a_with a pri') with aw. rewrite Epz2. apply (ext_sem_mono pz); [| exact Hjmono | | | | | exact Hbz]; unfold TTz.
    - exact (step_sb pz c Hlenz Hcr). - exact (step_qn pz c Hlenz Hcr). - exact (step_qj pz c Hlenz Hcr).
    - exact (step_gn pz c Hlenz Hcr). - exact (step_gl pz c Hlenz Hcr). }
  (* [comment removed for export] *)
  assert (Hext_fr : forall b z, ext_sem (pden E a) b z -> forall x, b <= x < b + z -> hyb (wa x) = mem0 (wa x)).
  { intros b z Hbz x Hxr. destruct (ext_sem_pt pz mem0 HI b z x Hbz Hxr) as (Rx & Hap & _ & HnQ & HnG).
    apply (Hhyb_out x ltac:(clear - Rx; lia)). intros Hn.
    apply (proj1 (proj2 (Hvf x ltac:(destruct (Hfuc_v x Hn) as [Hv|[Hv|Hv]]; [unfold VOWN in Hv; clear - Hv; tauto | clear - Hv; tauto | clear - Hv; tauto])))). exact Hap. }
  pose proof (HA_pri_step (s_next S) E E3 M a mem0 hyb pri' HA0 Haw Ha35 Hne Hne' Hown_eq
                ltac:(change (a_with a pri') with aw; rewrite Epz2; exact HIz') Hbase Hmono Hdepf Hext_step Hext_fr) as HAw.
  pose proof (own_pt_with (s_next S) E E3 M a mem0 hyb pri' HA0 Haw Ha35 Hne Hown_eq
                ltac:(change (a_with a pri') with aw; rewrite Epz2; exact HIz') Hbase Hmono) as Hsub.
  change (a_with a pri') with aw in HAw, Hsub.
  (* [comment removed for export] *)
  assert (HQJ : 1 <= z_qn pz -> 0 <= z_qj pz < 32 /\ z_qj pz < z_j pz 24).
  { intros Hq1. destruct (iz_q _ _ HI) as [(_ & _ & [(Q0 & _)|(_ & Q2 & _)]) Hqj]; [clear - Q0 Hq1; lia | split; [exact Q2 | exact (Hqj Hq1)]]. }
  assert (HGL : 1 <= z_gn pz -> 0 <= z_gl pz < 32 /\ z_gl pz < z_j pz 24).
  { intros Hg1. destruct (iz_gq _ _ HI) as [(_ & _ & _ & _ & _ & _ & _ & _ & [(G0 & _)|(_ & G2 & _)]) Hgl]; [clear - G0 Hg1; lia | split; [exact G2 | exact (Hgl Hg1)]]. }
  assert (Hbat : forall q, 0 <= q < 32 -> q < z_j pz 24 ->
            CHB + ND <= SB + 103079215104 + 8192 * q \/ SB + 103079215104 + 8192 * q + 8192 <= CHB).
  { intros q Hq0 Hq1. assert (Hsj : 0 <= sz_tbl c * z_j pz c /\ sz_tbl c * z_j pz c + sz_tbl c <= 262144) by (clear - K0 Hszp Hjn Hnm; nia).
    destruct (Z.eq_dec c 24) as [E24|N24].
    - right. unfold CHB. rewrite E24 in *. change (sz_tbl 24) with 8192. clear - Hq1. lia.
    - assert (D : c <= 23 \/ 25 <= c) by (clear - N24; lia). destruct D as [D|D]; [left | right]; unfold CHB; clear - D Hsj HND Hq0; lia. }
  assert (Hext : a_pri aw <> [] -> ext_sem (pden E3 aw) (uE E3 chl) (uE E3 ndl)).
  { intros _. rewrite Epz2, Ech3, End3. unfold TTz. split; [|split].
    - exists c. split; [exact Hcin|]. rewrite (step_sb pz c Hlenz Hcr), (step_j_same pz c Hlenz Hcr). destruct HCHB as (_ & _ & Bh3). fold SB.
      split; [unfold CHB; clear - K0 Hszp; nia|]. split; [unfold CHB; clear - HND Hszp; nia | exact Bh3].
    - rewrite (step_sb pz c Hlenz Hcr), (step_qn pz c Hlenz Hcr), (step_qj pz c Hlenz Hcr). fold SB. intros Hq1. destruct (HQJ Hq1) as [Q0 Q1]. exact (Hbat _ Q0 Q1).
    - rewrite (step_sb pz c Hlenz Hcr), (step_gn pz c Hlenz Hcr), (step_gl pz c Hlenz Hcr). fold SB. intros Hg1. destruct (HGL Hg1) as [Q0 Q1]. exact (Hbat _ Q0 Q1). }
  (* [comment removed for export] *)
  assert (Hnew : a_pri aw <> [] -> forall q, In q (x_rngs E3 aw) -> forall x, ~ (uE E3 chl <= x < uE E3 chl + uE E3 ndl /\ in_rg q x)).
  { intros _ q Hq x [X1 X2]. rewrite Ech3, End3 in X1.
    change (x_rngs E3 aw) with (x_rngs E3 a) in Hq. rewrite (x_rngs_agree _ E E3 a Haw Ha35) in Hq.
    destruct (x_rngs_ext_sem E a mem0 pz (po_ext _ _ _ _ HP0) (proj1 (po_lv _ _ _ _ HP0)) q Hq x X2) as (b0 & z0 & Hs0 & Hr0).
    apply (new_chunk_apart pz mem0 c b0 z0 x HI Hcin Hs0 Hr0). unfold CHB in X1. clear - X1 HND Hszp. nia. }
  pose proof (HA_on_ext_add E3 (with_own M (a_own aw)) aw hyb chl ndl HAw Hext Hnew) as HA'.
  (* [comment removed for export] *)
  set (Y4 := addo_post (addo_post Y2 RSh) RCh) in *.
  assert (Hneaw : a_pri aw <> []) by exact Hne'.
  pose proof (ha_pri _ _ _ _ HAw Hneaw) as HPa'.
  assert (Hfoot_new : forall w, pri_foot_z (pz_step pz c) w -> pri_foot_z pz w \/ RBv <= w < RBv + 262144 \/ FAv <= w < FAv + 262144).
  { intros w Hf. unfold pri_foot_z in *. rewrite (step_ca pz c Hlenz Hcr), (step_sb pz c Hlenz Hcr), (step_sh pz c Hlenz Hcr) in Hf.
    destruct Hf as [Hf|[Hf|[Hf|(c' & Hc' & Hf)]]]; [left; left; exact Hf | left; right; left; exact Hf | left; right; right; left; exact Hf |].
    destruct (Z.eq_dec c' c) as [->|Hnc].
    - rewrite (step_z_same pz c Hlenz Hcr) in Hf. fold SB in Hf. destruct Hf as [Hf|[Hf|Hf]]; [right; left; exact Hf | right; right; exact Hf |].
      left. right. right. right. exists c. split; [exact Hcin|]. right. right. exact Hf.
    - rewrite (step_z_other pz c Hlenz Hcr c' (in_cls_rng c' Hc') Hnc) in Hf. left. right. right. right. exists c'. split; [exact Hc' | exact Hf]. }
  assert (Hown_M4 : forall w, own_pt E M w -> own_pt E3 M4 w).
  { intros w (p & Hp & Hpw). exists p. split; [exact (Hsub4 p Hp)|].
    pose proof (sm_wf_own _ M HwfM) as Hfw. rewrite Forall_forall in Hfw. destruct (Hfw p Hp) as [Hf1 Hf2]. cbn [L np_front s_next] in Hf1, Hf2.
    rewrite (uE_agree (s_next S) E E3 _ Hf1 Ha35), (uE_agree (s_next S) E E3 _ Hf2 Ha35). exact Hpw. }
  assert (Hown_maps : forall w, RBv <= w < RBv + 262144 \/ FAv <= w < FAv + 262144 -> own_pt E3 M4 w).
  { intros w [Hr|Hr].
    - exists (rbg, lconst 262144). split; [cbn [M4 M2 with_own sm_own]; apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
      cbn [fst snd]. rewrite (uE_agree n0 E E3 _ Hwrb Ha35g), Erb, uE_lc by (clear; lia). exact Hr.
    - exists (fag, lconst 262144). split; [cbn [M4 with_own sm_own]; apply in_or_app; right; left; reflexivity|].
      cbn [fst snd]. rewrite (uE_agree n0 E E3 _ Hwfa Ha35g), Efa, uE_lc by (clear; lia). exact Hr. }
  assert (HD11 : DEN ASEGS LIMIT model0 hyb E3 Y4 (with_own M (a_own aw)) ms5 model5).
  { change (with_own M (a_own aw)) with (with_own M4 (a_own aw)).
    apply (den_own_set ASEGS LIMIT model0 hyb hyb E3 Y4 M4 ms5 model5 (a_own aw) HD10).
    - pose proof Cawf as XW. unfold awf in XW. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [_ XW].
      exact XW.
    - intros w _. reflexivity.
    - intros w Hw. destruct (Hown4 w Hw) as [Hm|Hr]; [exact (Hsub w Hm)|].
      apply (po_own _ _ _ _ HPa' w); [unfold RBv, FAv in Hr; clear - Hr B0 Hcr; lia|].
      unfold pri_foot. rewrite Epz2. unfold TTz, pri_foot_z. rewrite (step_ca pz c Hlenz Hcr), (step_sb pz c Hlenz Hcr), (step_sh pz c Hlenz Hcr).
      right. right. right. exists c. split; [exact Hcin|]. rewrite (step_z_same pz c Hlenz Hcr). fold SB. unfold RBv, FAv in Hr. clear - Hr. lia.
    - intros w (q & Hq & Hqw). cbn [with_own sm_own] in Hq.
      assert (Hw4 : own_pt E3 M4 w).
      { rewrite (ha_aown _ _ _ _ HAw) in Hq. unfold aown_of in Hq. apply in_app_or in Hq as [Hq|Hq].
        - apply Hown_M4. exists q. split.
          + rewrite Hown_eq, (ha_aown _ _ _ _ HA0). unfold aown_of. apply in_or_app. left. exact Hq.
          + assert (Hpw : pwf (s_next S) q = true).
            { pose proof Haw as XW. unfold awf in XW. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [_ XW].
              rewrite forallb_forall in XW. apply XW. rewrite (ha_aown _ _ _ _ HA0). unfold aown_of. apply in_or_app. left. exact Hq. }
            unfold pwf in Hpw. apply andb_prop in Hpw as [Hp1 Hp2]. rewrite <- (uE_agree _ E E3 _ Hp1 Ha35), <- (uE_agree _ E E3 _ Hp2 Ha35). exact Hqw.
        - assert (Hq' : In q (pri_own aw)) by (change (a_pri aw) with pri' in Hq; destruct pri'; [destruct Hq | exact Hq]).
          pose proof (pri_own_foot E3 aw hyb ltac:(unfold INV_A; rewrite Epz2; exact HIz') q Hq' w Hqw) as Hf.
          unfold pri_foot in Hf. rewrite Epz2 in Hf. destruct (Hfoot_new w Hf) as [Hf0|Hr]; [|exact (Hown_maps w Hr)].
          apply Hown_M4. apply (po_own _ _ _ _ HP0 w); [pose proof (pri_foot_rng E a mem0 HI w Hf0) as Rfw; clear - Rfw; lia | exact Hf0]. }
      destruct Hw4 as (q0 & Hq0 & Hq0w). exact (dn_own _ _ _ _ _ _ _ _ _ HD10 q0 Hq0 w Hq0w). }
  apply (Hk E3 hyb ms5 model5).
  - exact Ha35.
  - intros q Hq w Hw. destruct (Hfrz0 w (ex_intro _ q (conj Hq Hw))) as [Hw6 Hnf0]. exact (Hhyb_out w Hw6 Hnf0).
  - exact HD11.
  - intros _. exact HA'.
Qed.
End NPopGFirst.
