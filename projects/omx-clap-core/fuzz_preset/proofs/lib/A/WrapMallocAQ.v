(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/A/WrapMallocAQ.v, with its module paths and module names changed. *)
(* Theorem Labs, 2026-10-31: omx-clap-core/fuzz_preset image A (asan, pin 1be0f53d96cb): the relation the A' malloc walk
   and the malloc body are stated at, ARXq_A B := YGcfInstBase.ARXq_cf B IOK at IOK := (fun i => i = as_inst B) and
   AImg_A (im_segs := tfibsegs). It is the relation of a Theorem Labs lane's A' Allocate contract aalloc_realizes_cf_em_m_A
   (a working branch b43cbafb0c8, lib/A/AllocGtopPresetM.v:287 ARXc := ARXq_cf B IOK) at preset's
   IOK (YGcfInstBase.v:589-593; IOK_ok by `fun i H => H`), so the walk composes with it with no bridge
   (a Theorem Labs lane's ruling, 2026-10-31 03:33Z). The facts the walks need of it: the two hypotheses of the generic
   return segment (ARX_ARcf, the step's model change), ARX_xs, and its derivation from the walk-side ARXh_A at
   Allocate's entry. No Admitted / Axiom. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AImgA.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfXs YGcfXsMapped.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m WrapMallocADefs.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section c.
Variable B : asyms.

Definition ARXq_A : YGcfMallocCompose.ARXh_t tfibsegs := YGcfInstBase.ARXq_cf (IM := AImgA.AImg_A) B (fun i => i = as_inst B).

Lemma ARXq_A_HXA : YGcfMallocCompose.ARX_ARcf tfibsegs B ARXq_A.
Proof. intros Hp inst ly S W mem md H. exact (proj1 (proj2 (proj1 H))). Qed.

Lemma ARXq_A_HXF : forall Hp inst ly S W mem md mem' mat,
  ARXq_A Hp inst ly S W mem md ->
  ARcf tfibsegs B ly S Hp W mem' (with_vm_backing (m_vm_lazy md) mat md) ->
  ARXq_A Hp inst ly S W mem' (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros Hp inst ly S W mem md mem' mat ((I & _ & XM) & Q) A.
exact (conj (conj I (conj A (xs_mapped_cf_wvb ly S md (m_vm_lazy md) mat XM))) Q).
Qed.

Lemma ARXq_A_xs : ARX_xs tfibsegs ARXq_A.
Proof. exact (YGcfInstBase.ARXq_cf_xs (IM := AImgA.AImg_A) B (fun i => i = as_inst B)). Qed.

(* ARXh_A gives ARXq_A at the same arguments: the instance equation, ARcf, xs_mapped_cf from ARcf (YGcfXs.ARcf_xsm),
   and qtight from ARXh_A's qmeter_cf (YG0ncf.v: qmeter_cf S := qtight S /\ mroom_cf S). *)
Lemma ARXq_A_of_h : forall Hp inst ly S W mem md, ARXh_A B Hp inst ly S W mem md -> ARXq_A Hp inst ly S W mem md.
Proof.
intros Hp inst ly S W mem md (I & A & QM & _).
exact (conj (conj I (conj A (ARcf_xsm tfibsegs B ly S Hp W mem md A))) (proj1 QM)).
Qed.

(* So Allocate's precondition at ARXh_A gives it at ARXq_A (its relation is alloc_pre's first conjunct). *)
Lemma malloc_apre_q_of_h : forall nmax al atp acf Hp inst so bp ly S W regs mem md n tr,
  malloc_apre_cf tfibsegs B nmax al atp acf (ARXh_A B) Hp inst so bp ly S W regs mem md n tr ->
  malloc_apre_cf tfibsegs B nmax al atp acf ARXq_A Hp inst so bp ly S W regs mem md n tr.
Proof.
intros nmax al atp acf Hp inst so bp ly S W regs mem md n tr [X R].
exact (conj (ARXq_A_of_h Hp inst ly S W mem md X) R).
Qed.
End c.
End a.
