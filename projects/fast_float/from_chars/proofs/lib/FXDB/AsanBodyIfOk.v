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
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require AsanMainSF AsanMainWF AsanLit.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImgScan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanImg OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTbl OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblM OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTblMd OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanPlan OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanStart OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanFinC OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2.AsanShort OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanEntry.AsanSegs OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainSF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanMainWF OSSVerify.Proofs.fast_float.from_chars.lib.FXGB.AsanLit.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcHA AcFam AcSubst AcSubstR AcPri AcFam2 AcFam3 AcFam3Ok AcMALlib AcShmRd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxMchr AsanQcsX AsanPNodes FxPNodesX AsanTblH2 AsanBodyE AsanBNodes AsanBodyFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanTblH2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanCallTE AsanCallTP AsanCallTL AsanBodyIf.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsX OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanPNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxPNodesX OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblH2 OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyFam OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanTblH2.AsanTailDefs OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTE OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTP OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTL OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanBodyIf.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require M4Pure HarnEnt HarnDev.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanCallTE.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require HETH.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanCallTP.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require HPFP HPTH HPFHARN.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.M4Pure OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnEnt OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnDev OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTE.HEFP OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HETH OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTP.HEFH OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HPFP OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HPTH OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HPFHARN.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require HarnSubsE HarnSubs.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HLB Require HarnSubs.
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
  - apply some_inj4 in Hj. destruct Hj as (<- & <- & <- & <-). first [exact (M4HB.HarnSubs.harn_prep_sub_ok cfg Hanode3 (cls_shadow_readable LIM) Hcons) | exact (M4HB.HarnSubs.harn_prep_sub_ok cfg Hoff Hanode3 (cls_shadow_readable LIM) Hcons)].
  - apply some_inj4 in Hj. destruct Hj as (<- & <- & <- & <-). first [exact (M4HLB.HarnSubs.harn_prep_sub_ok cfg Hanode3 (cls_shadow_readable LIM) Hcons) | exact (M4HLB.HarnSubs.harn_prep_sub_ok cfg Hoff Hanode3 (cls_shadow_readable LIM) Hcons)].
  - apply some_inj4 in Hj. destruct Hj as (<- & <- & <- & <-). exact (HarnSubsE.harn_sub_ok cfg Hanode3 (cls_shadow_readable LIM) Hcons).
  - apply some_inj4 in Hj. destruct Hj as (<- & <- & <- & <-). first [exact (M4HB.HarnSubs.harn_sub_ok cfg Hanode3 (cls_shadow_readable LIM) Hcons) | exact (M4HB.HarnSubs.harn_sub_ok cfg Hoff Hanode3 (cls_shadow_readable LIM) Hcons)].
  - apply some_inj4 in Hj. destruct Hj as (<- & <- & <- & <-). first [exact (M4HLB.HarnSubs.harn_sub_ok cfg Hanode3 (cls_shadow_readable LIM) Hcons) | exact (M4HLB.HarnSubs.harn_sub_ok cfg Hoff Hanode3 (cls_shadow_readable LIM) Hcons)].
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
(* [comment removed for export] *)
