(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require VmMapsDisjoint.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import LimBase LimFit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition linv (m : Model) : Prop := fits m /\ VmMapsDisjoint.vm_wf (m_vmmaps m).

Lemma linv_sl : forall L m, linv (sl L m) <-> linv m.
Proof. intros L m. unfold linv. reflexivity. Qed.

Lemma linv_sys : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) -> linv m -> linv m'.
Proof.
  intros i m eff m' evs H [HF HW]. split.
  - exact (syscall_spec_fits i m eff m' evs H HF).
  - exact (VmMapsDisjoint.syscall_spec_preserves_vm_wf i m eff m' evs H HW).
Qed.

Lemma linv_mat : forall m acc m',
  materialize_model_accesses m acc = Some m' -> linv m -> linv m'.
Proof.
  intros m acc m' H [HF HW].
  destruct (materialize_model_accesses_frame m acc m' H) as (_ & E & _).
  split; [exact (fits_vmmaps_eq m m' E HF) | rewrite E; exact HW].
Qed.

Lemma linv_init : forall reserved brk0 mbase sp lim inp,
  linv (init_model reserved brk0 mbase sp lim inp).
Proof.
  intros. split; [apply init_model_fits | apply VmMapsDisjoint.init_model_vm_wf].
Qed.

Lemma linv_nonzero : forall m, linv m ->
  Forall (fun e => bv_unsigned (snd e) <> 0) (vm_maps (m_vmmaps m)).
Proof. intros m [_ [H _]]. exact H. Qed.
