(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan Require Import CatSim ShapeAlg.
Import ListNotations.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Definition TSet : Type := config -> Prop.

Definition md_clean (MD : Model) : Prop :=
  m_vm_lazy MD = [] /\ m_vm_materialized MD = [].

Definition realizes (segs : list Segment) (c : config) (Q : TSet) : Prop :=
  exists ms', msteps segs (cfg_ms c) ms' /\ Q (mkCfg ms' (cfg_model c)).

Lemma rz_step : forall segs ms model ms' T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = RiscvSemantics.MachineOk ms' ->
  realizes segs (mkCfg ms' model) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros segs ms model ms' T Hh Hsvc Hstep (ms'' & Hrun & HQ). cbn [cfg_ms cfg_model] in *.
  exists ms''. split; [| exact HQ].
  eapply mst_step; [exact Hsvc | exact Hstep | exact Hrun].
Qed.

Lemma rz_now : forall segs ms model (Q : TSet),
  Q (mkCfg ms model) -> realizes segs (mkCfg ms model) Q.
Proof. intros segs ms model Q H. exists ms. split; [apply mst_refl | exact H]. Qed.

Lemma rz_msteps : forall segs ms model (Q : TSet),
  realizes segs (mkCfg ms model) Q ->
  exists ms', msteps segs ms ms' /\ Q (mkCfg ms' model).
Proof. intros segs ms model Q H. exact H. Qed.

Lemma rz_prefix : forall segs ms ms' model (Q : TSet),
  msteps segs ms ms' ->
  realizes segs (mkCfg ms' model) Q ->
  realizes segs (mkCfg ms model) Q.
Proof.
  intros segs ms ms' model Q Hrun (ms'' & Hrun' & HQ). cbn [cfg_ms cfg_model] in *.
  exists ms''. split; [eapply msteps_trans; eassumption | exact HQ].
Qed.

Lemma rz_conseq : forall segs c (Q Q' : TSet),
  realizes segs c Q -> (forall c', Q c' -> Q' c') -> realizes segs c Q'.
Proof. intros segs c Q Q' (ms' & H & HQ) Himp. exists ms'. split; [exact H | apply Himp; exact HQ]. Qed.
End FXG.
