(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChMain FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.FxChMap.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanTblML AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanPhases3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanLit AsanCpSW AsanPhases3 AsanErrT AsanPhT1.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblML OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainP.AsanMainG1F OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainP.AsanPhases OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainP OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhases3.AsanPhases2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanLit OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanCpSW OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhases3 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanErrT OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPhT1.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanPNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam AcSubst AcMALlib.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition CONTS0 : list (sst * smodel * fstate * shp * ast) := [PHT1_C; TERR_C].
Definition NB1 : positive := Eval vm_compute in s_next PHT1_S.
Definition CHAIN0 : MCF := MAINP4 (KERR 1) (GC (MCont 0 NB1)).     (* [comment removed for export] *)
Definition S1P2 : sst := S1c2 65536 GHI.
Definition ph0_res : option (list (sst * smodel * fstate * shp * ast)) :=
  mcheck ASEGS LIM TBLM IMGMd PV 65536 GHI false (Some H0) apostF anil aeqb awf acopy_alloc asubst ag_ok alins_a aset_a amod_a [] CONTS0 CHAIN0 S1P2 M1c FSClosed SHG A1c.
Definition ph0_chk : bool := is_some ph0_res.
(* [comment removed for export] *)
