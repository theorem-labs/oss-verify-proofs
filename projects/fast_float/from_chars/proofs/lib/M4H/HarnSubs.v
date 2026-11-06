(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxImg FxSubst FxLoop FxPlan FxFrame FxFacts FxEcall FxEnt FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChNull FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxWvC FxChEntM FxChSubst FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain.FxChSys OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEntM OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSubst OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanImgScan AsanImg AsanTbl AsanTblM AsanTblMd AsanEntry AsanPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanFinC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanEntry.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF AsanMainWF.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry.AsanSegs OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainWF.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcHA AcFam AcSubst AcSubstR AcPri AcFam2 AcFam3 AcMALlib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import FxMchr AsanQcsX AsanPNodes FxPNodesX AsanBodyE AsanBNodes.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require M4Pure HarnFam HarnChain HarnEnt HarnDev HarnSubCh HarnMain HarnCertFam HarnCertLib HarnPM2 HPFP HPTH HPFHARN HarnPrepCert HarnCrlsCert_G HarnCrlsSub_G.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanCallTP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanCallTP.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require HarnMidCert HarnMainCert.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4H.M4Pure OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnFam OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnChain OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnEnt OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnDev OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnSubCh OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnMain OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnCertFam OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnCertLib OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnPM2 OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HPFP OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HPTH OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HPFHARN OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnPrepCert OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnCrlsCert_G OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnCrlsSub_G OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanCallTP.HPMT OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanCallTP.HPMF OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnMidCert OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnMainCert.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma some_inj4 : forall {A B C D : Type} (a a' : A) (b b' : B) (c c' : C) (d d' : D),
  Some (a, b, c, d) = Some (a', b', c', d') -> a = a' /\ b = b' /\ c = c' /\ d = d'.
Proof. intros A B C D a a' b b' c c' d d' H. inversion H. repeat split; reflexivity. Qed.

Section HarnSubs.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hanode3 : forall nk, anode_ok ASEGS cfg LIM (AcFam3.apost_alloc3 LIM) awf HA nk.
Hypothesis Hshm : forall model0 mem0 E S M ms model a, DEN ASEGS LIM model0 mem0 E S M ms model -> HA_on E M a mem0 -> a_pri a <> [] ->
  forall c, In c CLS -> 1 <= z_j (pden E a) c ->
  forall x, z_sh (pden E a) + 536870912 * c <= x < z_sh (pden E a) + 536870912 * c + 32768 ->
  rd1 ASEGS (mrestrict (Hof E M model) (ms_mem ms)) (Z_to_bv 64 x) <> None.
Hypothesis Hcons : Forall (con_ok ASEGS) CONS.

#[using="Hanode3 Hshm Hcons"] Theorem harn_prep_sub_ok : sub_ok ASEGS cfg LIM awf HA ENT_S ENT_M ENT_A PREP_FINS.
Proof. LiaFast.lf_pins (fun (Hanode3 Hshm Hcons : LiaFast.U) => LiaFast.u0).
  refine (sub_ok_of_PCHK cfg Hanode3 Hshm Hcons [] _ HARN_PREP ENT_S ENT_M ENT_A PREP_FINS prep_cert).
  intros j T MT aT fins H. destruct j; discriminate H.
Qed.
#[using="Hanode3 Hshm Hcons"] Lemma mid_subs_ok : forall j T MT aT fins, nth_error MID_SUBS j = Some (T, MT, aT, fins) -> sub_ok ASEGS cfg LIM awf HA T MT aT fins.
Proof. LiaFast.lf_pins (fun (Hanode3 Hshm Hcons : LiaFast.U) => LiaFast.u0).
  intros j T MT aT fins H.
  destruct j as [|j]; cbn [nth_error MID_SUBS] in H; try (destruct j; discriminate H); apply some_inj4 in H; destruct H as (<- & <- & <- & <-).
  exact (crls_sub_ok_G cfg Hanode3 Hshm Hcons).
Qed.
(* [comment removed for export] *)
#[using="Hanode3 Hshm Hcons"] Theorem mid_sub_ok : sub_ok ASEGS cfg LIM awf HA HPMT_S HPMT_M HPMT_A MID_FINS.
Proof. LiaFast.lf_pins (fun (Hanode3 Hshm Hcons : LiaFast.U) => LiaFast.u0).
  exact (sub_ok_of_PCHK cfg Hanode3 Hshm Hcons MID_SUBS mid_subs_ok MID_CH HPMT_S HPMT_M HPMT_A MID_FINS mid_cert).
Qed.
#[using="Hanode3 Hshm Hcons"] Lemma harn_subs_ok : forall j T MT aT fins, nth_error HARN_SUBS j = Some (T, MT, aT, fins) -> sub_ok ASEGS cfg LIM awf HA T MT aT fins.
Proof. LiaFast.lf_pins (fun (Hanode3 Hshm Hcons : LiaFast.U) => LiaFast.u0).
  intros j T MT aT fins H.
  destruct j as [|j]; cbn [nth_error HARN_SUBS] in H; try (destruct j; discriminate H); apply some_inj4 in H; destruct H as (<- & <- & <- & <-).
  exact mid_sub_ok.
Qed.
#[using="Hanode3 Hshm Hcons"] Theorem harn_sub_ok : sub_ok ASEGS cfg LIM awf HA HPTH_S HPTH_M HPTH_A HARN_FINS.
Proof. LiaFast.lf_pins (fun (Hanode3 Hshm Hcons : LiaFast.U) => LiaFast.u0).
  exact (sub_ok_of_PCHK cfg Hanode3 Hshm Hcons HARN_SUBS harn_subs_ok HARN_CH HPTH_S HPTH_M HPTH_A HARN_FINS harn_cert).
Qed.
End HarnSubs.
