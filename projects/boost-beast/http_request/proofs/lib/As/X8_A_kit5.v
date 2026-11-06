(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsImgSh AsIface AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import N8Kit N8Kit2 N8Kit3 X8Kit X8SRKit X8_A_kit X8_A_kit2 X8_A_kit3 X8_A_kit4 X8_asio_stmt_reg.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma le4_m1 : le4 (Z_to_bv 64 18446744073709551615) = le4 (Z_to_bv 64 4294967295).
Proof. unfold le4. apply Z_to_le_bytes_4_congr. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sx32_m1' : sx32 (Z_to_bv 64 4294967295) = Z_to_bv 64 18446744073709551615.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma AXS_tiname_config : forall m, AXStatics2 m -> ro_cells asegs m (AL_TYPEID_CONFIG + 8) [C8 (wz ATI_NAME_CONFIG)].
Proof.
  intros m XS. destruct XS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H0 & _).
  unfold wcells in H0. cbn [map] in H0. exact (proj1 H0).
Qed.
Lemma AXS_tiname_sched : forall m, AXStatics2 m -> ro_cells asegs m (AL_TYPEID_SCHED + 8) [C8 (wz ATI_NAME_SCHED)].
Proof.
  intros m XS. destruct XS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H0 & _).
  unfold wcells in H0. cbn [map] in H0. exact (proj1 H0).
Qed.

(* [comment removed for export] *)
Lemma ati_ok_config : forall m, AXStatics2 m -> ati_ok m AL_TYPEID_CONFIG ATI_NAME_CONFIG.
Proof.
  intros m XS. split; [exact (AXS_tiname_config _ XS)|]. unfold ATI_NAME_CONFIG, AL_TYPEID_CONFIG.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. vm_compute. reflexivity.
Qed.
Lemma ati_ok_sched : forall m, AXStatics2 m -> ati_ok m AL_TYPEID_SCHED ATI_NAME_SCHED.
Proof.
  intros m XS. split; [exact (AXS_tiname_sched _ XS)|]. unfold ATI_NAME_SCHED, AL_TYPEID_SCHED.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma img_acc_allocimpl_vt8 : forall m, ACONST m -> accessible m (AVP_ALLOCIMPL + 8) 8.
Proof. intros m AC. apply (ACONST_img_accessible m _ _ AC). vm_compute. reflexivity. Qed.

Section W.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Lemma ARegistry_xpres_scratch : forall s LB m0 LF m1 SP XS m m' r owner first lk,
    as_RHEAP H s LB m0 -> as_RFS H LF m1 -> Forall (fs_scratch H LF) XS ->
    ARegistry LB m r owner first lk -> xpres H LB SP XS m m' -> ARegistry LB m' r owner first lk.
  Proof.
    intros s LB m0 LF m1 SP XS m m' r owner first lk RH RF FX P XP. pose proof P as (p & j0 & j7 & IN & _).
    destruct (scratch_off_blk H HH _ _ _ _ _ _ _ _ _ RH RF IN FX) as (F1 & F2).
    eapply (ARegistry_xpres H); [exact P| exact XP| exact F1| exact F2].
  Qed.

  Lemma AConfigSvc_xpres_scratch : forall s LB m0 LF m1 SP XS m m' c S,
    as_RHEAP H s LB m0 -> as_RFS H LF m1 -> Forall (fs_scratch H LF) XS ->
    AConfigSvc LB m c S -> xpres H LB SP XS m m' -> AConfigSvc LB m' c S.
  Proof.
    intros s LB m0 LF m1 SP XS m m' c S RH RF FX P XP. pose proof P as (p & j4 & j7 & IN & _).
    destruct (scratch_off_blk H HH _ _ _ _ _ _ _ _ _ RH RF IN FX) as (F1 & F2).
    eapply (AConfigSvc_xpres H); [exact P| exact XP| exact F1| exact F2].
  Qed.

  Lemma AScheduler_xpres_scratch : forall s LB m0 LF m1 SP XS m m' b S,
    as_RHEAP H s LB m0 -> as_RFS H LF m1 -> Forall (fs_scratch H LF) XS ->
    AScheduler LB m b S -> xpres H LB SP XS m m' -> AScheduler LB m' b S.
  Proof.
    intros s LB m0 LF m1 SP XS m m' b S RH RF FX P XP.
    pose proof P as (p & j50 & jm & j109 & je & jt & j219 & j7 & IN & _).
    destruct (scratch_off_blk H HH _ _ _ _ _ _ _ _ _ RH RF IN FX) as (F1 & F2).
    eapply (AScheduler_xpres H); [exact P| exact XP| exact F1| exact F2].
  Qed.

  (* [comment removed for export] *)
  Lemma ARegistry_xpres_app_scratch : forall s LB m0 LF m1 SP X XS m m' r owner first lk,
    as_RHEAP H s LB m0 -> as_RFS H LF m1 -> Forall noshadow X -> Forall (fs_scratch H LF) XS ->
    Forall (fun iv : Z * Z => r + NEWSZ_REG <= fst iv \/ snd iv <= r) X ->
    ARegistry LB m r owner first lk -> xpres H LB SP (X ++ XS) m m' -> ARegistry LB m' r owner first lk.
  Proof.
    intros s LB m0 LF m1 SP X XS m m' r owner first lk RH RF NS FX OFF P XP. pose proof P as (p & j0 & j7 & IN & _ & _ & _ & _ & RB & _).
    pose proof (rblock_bounds _ _ RB) as (B0 & B1 & B2 & _).
    destruct (scratch_off_blk H HH _ _ _ _ _ _ _ _ _ RH RF IN FX) as (F1 & F2).
    eapply (ARegistry_xpres H); [exact P| exact XP| apply Forall_app; split; [exact OFF| exact F1]|].
    apply Forall_app; split; [| exact F2]. apply noshadow_avoid_sh; [exact NS| lia| unfold NEWSZ_REG; lia| exact B2].
  Qed.

  Lemma AConfigSvc_xpres_app_scratch : forall s LB m0 LF m1 SP X XS m m' c S,
    as_RHEAP H s LB m0 -> as_RFS H LF m1 -> Forall noshadow X -> Forall (fs_scratch H LF) XS ->
    Forall (fun iv : Z * Z => c + NEWSZ_CFG <= fst iv \/ snd iv <= c) X ->
    AConfigSvc LB m c S -> xpres H LB SP (X ++ XS) m m' -> AConfigSvc LB m' c S.
  Proof.
    intros s LB m0 LF m1 SP X XS m m' c S RH RF NS FX OFF P XP. pose proof P as (p & j4 & j7 & IN & _ & _ & _ & RB & _).
    pose proof (rblock_bounds _ _ RB) as (B0 & B1 & B2 & _).
    destruct (scratch_off_blk H HH _ _ _ _ _ _ _ _ _ RH RF IN FX) as (F1 & F2).
    eapply (AConfigSvc_xpres H); [exact P| exact XP| apply Forall_app; split; [exact OFF| exact F1]|].
    apply Forall_app; split; [| exact F2]. apply noshadow_avoid_sh; [exact NS| lia| unfold NEWSZ_CFG; lia| exact B2].
  Qed.

  Lemma AScheduler_xpres_app_scratch : forall s LB m0 LF m1 SP X XS m m' b S,
    as_RHEAP H s LB m0 -> as_RFS H LF m1 -> Forall noshadow X -> Forall (fs_scratch H LF) XS ->
    Forall (fun iv : Z * Z => b + NEWSZ_SCH <= fst iv \/ snd iv <= b) X ->
    AScheduler LB m b S -> xpres H LB SP (X ++ XS) m m' -> AScheduler LB m' b S.
  Proof.
    intros s LB m0 LF m1 SP X XS m m' b S RH RF NS FX OFF P XP.
    pose proof P as (p & j50 & jm & j109 & je & jt & j219 & j7 & IN & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RB & _).
    pose proof (rblock_bounds _ _ RB) as (B0 & B1 & B2 & _).
    destruct (scratch_off_blk H HH _ _ _ _ _ _ _ _ _ RH RF IN FX) as (F1 & F2).
    eapply (AScheduler_xpres H); [exact P| exact XP| apply Forall_app; split; [exact OFF| exact F1]|].
    apply Forall_app; split; [| exact F2]. apply noshadow_avoid_sh; [exact NS| lia| unfold NEWSZ_SCH; lia| exact B2].
  Qed.

  Lemma AAllocImpl_xpres_app_scratch : forall s LB m0 LF m1 SP X XS m m' a,
    as_RHEAP H s LB m0 -> as_RFS H LF m1 -> Forall noshadow X -> Forall (fs_scratch H LF) XS ->
    Forall (fun iv : Z * Z => a + SZ_ALLOCIMPL <= fst iv \/ snd iv <= a) X ->
    AAllocImpl LB m a -> xpres H LB SP (X ++ XS) m m' -> AAllocImpl LB m' a.
  Proof.
    intros s LB m0 LF m1 SP X XS m m' a RH RF NS FX OFF P XP. pose proof P as (p & junk & IN & _ & RB & _).
    pose proof (rblock_bounds _ _ RB) as (B0 & B1 & B2 & _).
    destruct (scratch_off_blk H HH _ _ _ _ _ _ _ _ _ RH RF IN FX) as (F1 & F2).
    eapply (AAllocImpl_xpres H); [exact P| exact XP| apply Forall_app; split; [exact OFF| exact F1]|].
    apply Forall_app; split; [| exact F2]. apply noshadow_avoid_sh; [exact NS| lia| unfold SZ_ALLOCIMPL; lia| exact B2].
  Qed.

  (* [comment removed for export] *)
  Lemma ARegistry_cons_LB : forall LB b m r owner first lk, ARegistry LB m r owner first lk -> ARegistry (b :: LB) m r owner first lk.
  Proof. intros. eapply ARegistry_mono; [| eassumption]. intros; right; assumption. Qed.

End W.
End HCW.
