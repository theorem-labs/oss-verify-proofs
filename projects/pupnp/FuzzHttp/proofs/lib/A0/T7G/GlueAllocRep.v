(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image Ceiling.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import MainExport MainFactsAsan A0Img MainEntry A0Handoff.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ASec AQuar F_quar_M PEnv AHeap AInitReps.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7G Require Import GlueKit GlueIcpt GlueAllocKit GlueAllocLay.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section Rep.
Context {HC : HasCeiling}.
Variable V : nat -> Z.
Hypothesis AO : alayout_ok (AL_of V).
Variable m : mem.
Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.

#[using="HM"] Lemma prim_env_init : prim_env (AL_of V) m.
Proof.
  unfold prim_env, RIB, AL_of. cbn [al_space].
  mf V m HM (MCell (ZLit 721592) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))) H1.
  lcells V m HM 721600 [C4 (wz 4294967295); C4 (wz 0)] H2.
  mf V m HM (MCell (ZLit 721608) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))) H3.
  lcells V m HM 721616 [C1 (Z_to_bv 8 0)] H4.
  replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + K_SPACE) with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia.
  apply (rw_cells_app2 m 721592 [_] _ 721600 H1 eq_refl).
  apply (rw_cells_app2 m 721600 [_; _] _ 721608 H2 eq_refl).
  exact (rw_cells_app2 m 721608 [_] _ 721616 H3 eq_refl H4).
Qed.

#[using="HC AO HM"] Lemma RPRIM_of : RPRIM (AL_of V) prim0 m.
Proof.
  apply (RPRIM_init (AL_of V) AO m prim_env_init).
  - mf V m HM (MZero (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)) 4096) ZR.
    mf V m HM (MWr (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)) 4096) W0.
    pose proof W0 as (WA & _).
    change 4096%nat with (Z.to_nat 4096).
    apply (zero_run m _ _ 4096 _ 4096 ZR W0 0 4096); [lia| lia| lia| unfold RIB, AL_of; cbn [al_space]; lia| unfold RIB, AL_of; cbn [al_space]; lia| unfold RIB, AL_of; cbn [al_space]; lia| unfold RIB, AL_of; cbn [al_space]; lia].
  - mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 80)) 3088) ZR.
    mf V m HM (MWr (ZMul (ZLit 4096) (ZV 227)) 4096) W0.
    pose proof W0 as (WA & _).
    change 2960%nat with (Z.to_nat 2960).
    apply (zero_run m _ _ 3088 _ 4096 ZR W0 128 2960); unfold AL_of; cbn [al_thread at_thr]; lia.
Qed.

#[using="HM"] Lemma sec_env_init : sec_env (AL_of V) m.
Proof.
  unfold sec_env, AL_of. cbn [al_parr].
  split.
  { lcells V m HM constr:(SEC) [C8 (wz 4096)] H1.
    mf V m HM (MCell (ZLit 721632) 8 (ZMul (ZLit 4096) (ZV 226))) H2. mf V m HM (MCell (ZLit 721640) 8 (ZMul (ZLit 4096) (ZV 226))) H3.
    apply (rw_cells_app2 m 721624 [_] _ 721632 H1 eq_refl). exact (rw_cells_app2 m 721632 [_] _ 721640 H2 eq_refl H3). }
  split. { lcells V m HM 696504 [C8 (wz 704440)] H. exact H. }
  lcells V m HM 704440 [C8 (wz 103692)] H. exact H.
Qed.

#[using="V HM"] Lemma sec_vars_init : sec_vars (mkSEC [] 0) m.
Proof.
  unfold sec_vars. cbn [se_nres se_n se_chunks]. unfold se_n. cbn [se_chunks length Z.of_nat].
  split.
  { exists (wz 8388608), (wz 103692), (wz 0), (Z_to_bv 8 0), (repeat (Z_to_bv 8 0) 7), (wz 0), (wz 0), (wz 0), (wz 0).
    lcells V m HM constr:(SEC_VARS) [C8 (wz 8388608); C8 (wz 103692); C8 (wz 0); C8 (wz 0); C8 (wz 0); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7);
                                     C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] H. exact H. }
  split.
  { exists (repeat (wz 0) 64). split; [| reflexivity]. split.
    - apply (lit_bytes_at V m asan_mem_facts); [exact HM| vm_compute; reflexivity| lia| vm_compute; discriminate].
    - apply a0_rw_image_wr_at; [lia| cbn; lia]. }
  split. { lcells V m HM constr:(SEC_MTX) [CB 4 [b8 0; b8 0; b8 0; b8 0]] H. exact H. }
  exists (wz 0), (wz 0). lcells V m HM constr:(GSTATS_A) [C8 (wz 0); C8 (wz 0)] H. exact H.
Qed.

#[using="AO HM"] Lemma RSEC_of : RSEC (AL_of V) (mkSEC [] 0) m.
Proof. exact (RSEC_init (AL_of V) AO m 0 sec_env_init sec_vars_init eq_refl). Qed.

#[using="HM"] Lemma quar_gq_init : rw_cells asegs m QUAR_GQ (qcells (AL_of V) []).
Proof. lcells V m HM constr:(QUAR_GQ) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] H. exact H. Qed.

#[using="HM"] Lemma quar_tq_init : rw_cells asegs m (at_thr (al_thread (AL_of V)) + TQ_OFF) (qcells (AL_of V) []).
Proof.
  mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 80)) 3088) ZR.
  mf V m HM (MWr (ZMul (ZLit 4096) (ZV 227)) 4096) W0. pose proof W0 as (WA & _).
  pose proof (zero_run m (4096 * V 227%nat + 80) _ 3088 _ 4096 ZR W0 0 32 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as R.
  change (Z.to_nat 32) with 32%nat in R.
  pose proof (rw_zeros_cells m _ 32 0 [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] R ltac:(cbn; tauto) ltac:(vm_compute; reflexivity) ltac:(cbn; lia)) as R2.
  rewrite Z.add_0_r in R2. exact R2.
Qed.

#[using="V HM"] Lemma quar_mtx_init : rw_cells asegs m QUAR_MTX [CB 4 [b8 0; b8 0; b8 0; b8 0]].
Proof. lcells V m HM constr:(QUAR_MTX) [CB 4 [b8 0; b8 0; b8 0; b8 0]] H. exact H. Qed.
End Rep.
