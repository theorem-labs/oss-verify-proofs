(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Definition model_ok (md : Model) : Prop := m_halted md = None /\ m_vm_lazy md = [].

Definition RZ (md : Model) (T : TSet) : machine_state -> Prop :=
fun ms' => realizes segs (mkCfg ms' md) T.

#[using="Type"] Lemma rz_mstep : forall ms ms' md T,
model_ok md -> mstep segs ms ms' ->
realizes segs (mkCfg ms' md) T -> realizes segs (mkCfg ms md) T.
Proof.
intros ms ms' md T [Hh Hl] [Hsvc Hst] Hr.
eapply rz_step; eauto.
Qed.

#[using="Type"] Lemma rz_msteps_lib : forall ms ms' md T,
model_ok md -> msteps segs ms ms' ->
realizes segs (mkCfg ms' md) T -> realizes segs (mkCfg ms md) T.
Proof.
intros ms ms' md T Hmd Hms. induction Hms as [ms | ms ms1 ms2 H1 H2 IH]; intros Hr.
- exact Hr.
- eapply rz_mstep; [exact Hmd | exact H1 | apply IH; exact Hr].
Qed.

#[using="Type"] Lemma rz_evt : forall ms md T,
model_ok md ->
evt segs (RZ md T) ms ->
realizes segs (mkCfg ms md) T.
Proof.
intros ms md T Hmd (ms' & Hms & Hr). eapply rz_msteps_lib; eauto.
Qed.

#[using="Type"] Lemma evt_RZ_done : forall ms md T,
realizes segs (mkCfg ms md) T -> evt segs (RZ md T) ms.
Proof. intros. apply evt_done. exact H. Qed.

End WithSegs.

Arguments model_ok md /.

Ltac kcall SPEC :=
lazymatch goal with
| |- evt ?segs (RZ _ ?md ?T) ?ms => apply evt_RZ_done; eapply SPEC
| |- realizes ?segs (mkCfg ?ms ?md) ?T => eapply SPEC
end.
