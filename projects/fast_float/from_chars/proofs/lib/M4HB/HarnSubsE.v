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
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall FxEnt FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChEntM FxChSubst FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSubst OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan AsanStart AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanEntry.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry.AsanSegs OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcHA AcFam AcSubst AcSubstR AcPri AcFam2 AcFam3 AcMALlib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import FxMchr AsanQcsX AsanPNodes FxPNodesX AsanBodyE AsanBNodes AsanCallTE.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require M4Pure HarnFam HarnChain HarnEnt HarnDev HarnSubCh HarnMain HarnMainE HarnCertFam HarnCertLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanCallTE.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require HETH.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanCallTP.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require HarnPrepCertE HarnMainCertE.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.M4Pure OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnFam OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnChain OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnEnt OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnDev OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnSubCh OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnMain OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnMainE OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnCertFam OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnCertLib OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTE.HEFP OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HETH OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTP.HEFH OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnPrepCertE OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnMainCertE.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HarnSubsE.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hanode3 : forall nk, anode_ok ASEGS cfg LIM (AcFam3.apost_alloc3 LIM) awf HA nk.
Hypothesis Hshm : forall model0 mem0 E S M ms model a, DEN ASEGS LIM model0 mem0 E S M ms model -> HA_on E M a mem0 -> a_pri a <> [] ->
  forall c, In c CLS -> 1 <= z_j (pden E a) c ->
  forall x, z_sh (pden E a) + 536870912 * c <= x < z_sh (pden E a) + 536870912 * c + 32768 ->
  rd1 ASEGS (mrestrict (Hof E M model) (ms_mem ms)) (Z_to_bv 64 x) <> None.
Hypothesis Hcons : Forall (con_ok ASEGS) CONS.

#[using="Hanode3 Hshm Hcons"] Theorem harn_prep_sub_ok : sub_ok ASEGS cfg LIM awf HA TCE_S TCE_M TCE_A PREP_FINS.
Proof. LiaFast.lf_pins (fun (Hanode3 Hshm Hcons : LiaFast.U) => LiaFast.u0).
  refine (sub_ok_of_PCHK cfg Hanode3 Hshm Hcons [] _ HARN_PREP_E TCE_S TCE_M TCE_A PREP_FINS prep_cert).
  intros j T MT aT fins H. destruct j; discriminate H.
Qed.
#[using="Hanode3 Hshm Hcons"] Theorem harn_sub_ok : sub_ok ASEGS cfg LIM awf HA HETH_S HETH_M HETH_A HARN_FINS.
Proof. LiaFast.lf_pins (fun (Hanode3 Hshm Hcons : LiaFast.U) => LiaFast.u0).
  refine (sub_ok_of_PCHK cfg Hanode3 Hshm Hcons [] _ HARN_CH HETH_S HETH_M HETH_A HARN_FINS harn_cert).
  intros j T MT aT fins H. destruct j; discriminate H.
Qed.
End HarnSubsE.
(* [comment removed for export] *)
