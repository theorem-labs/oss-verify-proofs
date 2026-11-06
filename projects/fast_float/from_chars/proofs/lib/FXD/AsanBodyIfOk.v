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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF AsanMainWF AsanLit.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanEntry.AsanSegs OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanLit.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcAst AcHA AcFam AcSubst AcSubstR AcPri AcFam2 AcFam3 AcFam3Ok AcMALlib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcDepDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcSubst OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcSubstR OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam2 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam3 OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcFam3Ok OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDepDen.AcShmRd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxMchr AsanQcsX AsanPNodes FxPNodesX AsanTblH2 AsanBodyE AsanBNodes AsanBodyFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanTblH2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanCallTP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanCallTP AsanCallTL AsanBodyIf.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQcsX OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxPNodesX OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTblH2 OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBodyE OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBodyFam OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanTblH2.AsanTailDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanCallTP.AsanCallTE OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanCallTP OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanCallTL OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanBodyIf.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require M4Pure HarnEnt HarnDev.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanCallTP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanCallTP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanCallTP.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require HPFP HPTH HPFHARN.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4H.M4Pure OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnEnt OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnDev OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanCallTP.HEFP OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanCallTP.HETH OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanCallTP.HEFH OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HPFP OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HPTH OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HPFHARN.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require HarnSubsE HarnSubs.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HL Require HarnSubs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Lemma some_inj1 : forall {A : Type} (a a' : A), Some a = Some a' -> a = a'.
Proof. intros A a a' H. inversion H. reflexivity. Qed.
Local Lemma some_inj4 : forall {A B C D : Type} (a a' : A) (b b' : B) (c c' : C) (d d' : D), Some (a, b, c, d) = Some (a', b', c', d') -> a = a' /\ b = b' /\ c = c' /\ d = d'.
Proof. intros A B C D a a' b b' c c' d d' H. inversion H. auto. Qed.

(* [comment removed for export] *)
Definition harn_hyps (cfg : SpuriousCfg) : Prop :=
  Forall (con_ok ASEGS) CONS.

Section IfOk.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hharn : harn_hyps cfg.

#[using="Hoff"] Lemma anodeX_ok : forall nk, anode_ok ASEGS cfg LIM apostX awf HA nk.
Proof. LiaFast.lf_pins (fun (Hoff : LiaFast.U) => LiaFast.u0). exact (anodeB_ok cfg (alloc3_anode_ok cfg LIM A_wx A_segb Hoff A_respos A_reswf) (cls_shadow_readable LIM)). Qed.

#[using="Hoff Hharn"] Lemma subsH_ok : forall j T MT aT fins, nth_error SUBS_H j = Some (T, MT, aT, fins) -> sub_ok ASEGS cfg LIM awf HA T MT aT fins.
Proof. LiaFast.lf_pins (fun (Hoff Hharn : LiaFast.U) => LiaFast.u0).
  intros j T MT aT fins Hj. pose proof Hharn as Hcons. unfold harn_hyps in Hcons.
  pose proof (alloc3_anode_ok cfg LIM A_wx A_segb Hoff A_respos A_reswf) as Hanode3.
  destruct j as [|[|[|[|[|[|j]]]]]]; cbn [nth_error SUBS_H] in Hj.
  - apply some_inj4 in Hj. destruct Hj as (<- & <- & <- & <-). exact (HarnSubsE.harn_prep_sub_ok cfg Hanode3 (cls_shadow_readable LIM) Hcons).
  - apply some_inj4 in Hj. destruct Hj as (<- & <- & <- & <-). first [exact (M4H.HarnSubs.harn_prep_sub_ok cfg Hanode3 (cls_shadow_readable LIM) Hcons) | exact (M4H.HarnSubs.harn_prep_sub_ok cfg Hoff Hanode3 (cls_shadow_readable LIM) Hcons)].
  - apply some_inj4 in Hj. destruct Hj as (<- & <- & <- & <-). first [exact (M4HL.HarnSubs.harn_prep_sub_ok cfg Hanode3 (cls_shadow_readable LIM) Hcons) | exact (M4HL.HarnSubs.harn_prep_sub_ok cfg Hoff Hanode3 (cls_shadow_readable LIM) Hcons)].
  - apply some_inj4 in Hj. destruct Hj as (<- & <- & <- & <-). exact (HarnSubsE.harn_sub_ok cfg Hanode3 (cls_shadow_readable LIM) Hcons).
  - apply some_inj4 in Hj. destruct Hj as (<- & <- & <- & <-). first [exact (M4H.HarnSubs.harn_sub_ok cfg Hanode3 (cls_shadow_readable LIM) Hcons) | exact (M4H.HarnSubs.harn_sub_ok cfg Hoff Hanode3 (cls_shadow_readable LIM) Hcons)].
  - apply some_inj4 in Hj. destruct Hj as (<- & <- & <- & <-). first [exact (M4HL.HarnSubs.harn_sub_ok cfg Hanode3 (cls_shadow_readable LIM) Hcons) | exact (M4HL.HarnSubs.harn_sub_ok cfg Hoff Hanode3 (cls_shadow_readable LIM) Hcons)].
  - destruct j; discriminate Hj.
Qed.
End IfOk.

(* [comment removed for export] *)
Lemma subsH_okU (cfg : SpuriousCfg) (Hoff : sc_alloc cfg = false) (Hharn : harn_hyps cfg) :
  forall j T MT aT fins, nth_error SUBS_H j = Some (T, MT, aT, fins) -> sub_ok ASEGS cfg LIM awf HA T MT aT fins.
Proof. first [exact (subsH_ok cfg Hoff Hharn) | exact (subsH_ok cfg Hharn)]. Qed.
(* [comment removed for export] *)
Lemma subsHE_okU (cfg : SpuriousCfg) (Hoff : sc_alloc cfg = false) (Hharn : harn_hyps cfg) :
  forall j T MT aT fins, nth_error SUBS_HE j = Some (T, MT, aT, fins) -> sub_ok ASEGS cfg LIM awf HA T MT aT fins.
Proof.
  intros j T MT aT fins Hj.
  destruct j as [|j]; [cbn [nth_error SUBS_HE] in Hj; unfold SUBH_E0, SUBH_E1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 0%nat _ _ _ _ eq_refl)|].
  destruct j as [|j]; [cbn [nth_error SUBS_HE] in Hj; unfold SUBH_E0, SUBH_E1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 0%nat _ _ _ _ eq_refl)|].
  destruct j as [|j]; [cbn [nth_error SUBS_HE] in Hj; unfold SUBH_E0, SUBH_E1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 0%nat _ _ _ _ eq_refl)|].
  destruct j as [|j]; [cbn [nth_error SUBS_HE] in Hj; unfold SUBH_E0, SUBH_E1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 3%nat _ _ _ _ eq_refl)|].
  destruct j as [|j]; [cbn [nth_error SUBS_HE] in Hj; unfold SUBH_E0, SUBH_E1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 3%nat _ _ _ _ eq_refl)|].
  destruct j as [|j]; [cbn [nth_error SUBS_HE] in Hj; unfold SUBH_E0, SUBH_E1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 3%nat _ _ _ _ eq_refl)|].
  cbn [nth_error SUBS_HE] in Hj. destruct j; discriminate Hj.
Qed.
Lemma subsHP_okU (cfg : SpuriousCfg) (Hoff : sc_alloc cfg = false) (Hharn : harn_hyps cfg) :
  forall j T MT aT fins, nth_error SUBS_HP j = Some (T, MT, aT, fins) -> sub_ok ASEGS cfg LIM awf HA T MT aT fins.
Proof.
  intros j T MT aT fins Hj.
  destruct j as [|j]; [cbn [nth_error SUBS_HP] in Hj; unfold SUBH_P0, SUBH_P1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 1%nat _ _ _ _ eq_refl)|].
  destruct j as [|j]; [cbn [nth_error SUBS_HP] in Hj; unfold SUBH_P0, SUBH_P1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 1%nat _ _ _ _ eq_refl)|].
  destruct j as [|j]; [cbn [nth_error SUBS_HP] in Hj; unfold SUBH_P0, SUBH_P1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 1%nat _ _ _ _ eq_refl)|].
  destruct j as [|j]; [cbn [nth_error SUBS_HP] in Hj; unfold SUBH_P0, SUBH_P1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 4%nat _ _ _ _ eq_refl)|].
  destruct j as [|j]; [cbn [nth_error SUBS_HP] in Hj; unfold SUBH_P0, SUBH_P1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 4%nat _ _ _ _ eq_refl)|].
  destruct j as [|j]; [cbn [nth_error SUBS_HP] in Hj; unfold SUBH_P0, SUBH_P1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 4%nat _ _ _ _ eq_refl)|].
  cbn [nth_error SUBS_HP] in Hj. destruct j; discriminate Hj.
Qed.
Lemma subsHL_okU (cfg : SpuriousCfg) (Hoff : sc_alloc cfg = false) (Hharn : harn_hyps cfg) :
  forall j T MT aT fins, nth_error SUBS_HL j = Some (T, MT, aT, fins) -> sub_ok ASEGS cfg LIM awf HA T MT aT fins.
Proof.
  intros j T MT aT fins Hj.
  destruct j as [|j]; [cbn [nth_error SUBS_HL] in Hj; unfold SUBH_L0, SUBH_L1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 2%nat _ _ _ _ eq_refl)|].
  destruct j as [|j]; [cbn [nth_error SUBS_HL] in Hj; unfold SUBH_L0, SUBH_L1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 2%nat _ _ _ _ eq_refl)|].
  destruct j as [|j]; [cbn [nth_error SUBS_HL] in Hj; unfold SUBH_L0, SUBH_L1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 2%nat _ _ _ _ eq_refl)|].
  destruct j as [|j]; [cbn [nth_error SUBS_HL] in Hj; unfold SUBH_L0, SUBH_L1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 5%nat _ _ _ _ eq_refl)|].
  destruct j as [|j]; [cbn [nth_error SUBS_HL] in Hj; unfold SUBH_L0, SUBH_L1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 5%nat _ _ _ _ eq_refl)|].
  destruct j as [|j]; [cbn [nth_error SUBS_HL] in Hj; unfold SUBH_L0, SUBH_L1 in Hj; apply some_inj4 in Hj; destruct Hj as (<- & <- & <- & <-); exact (subsH_okU cfg Hoff Hharn 5%nat _ _ _ _ eq_refl)|].
  cbn [nth_error SUBS_HL] in Hj. destruct j; discriminate Hj.
Qed.
