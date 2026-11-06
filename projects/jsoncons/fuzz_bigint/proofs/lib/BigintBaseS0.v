(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import HeapIface LibIface L5Defs L5CoreSpecs
     L5DivSpecs L5DivSpecsU L5DivSpecsO L5DivParts L5OpMod1Tail
     L5Norm L5NormOk L5Cmp L5Shr L5Reduce L5ReduceG
     L5Resize L5Assign L5Opdel
     L5Shrz L5DivEq L5Unnorm L5DivLoop L5DivTail L5DivNOkI L5OpMod1 L5OpMod2
     L5UnwindSpecs L5UnwindSpecsU L5Top L5TopU L5Layout L5TopBind L5TopBindU BigintFinal BigintFinalA BigintBaseH BigintBaseHA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import HeapInst0 HeapInst1 HeapClosed.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Src0.
Variable sptop : Z.
Hypothesis W : sptop_window sptop.
Let L := L0 sptop.
Let HI := HI0 sptop.
Let LY : L5CS.layout L := L0_layout sptop.
Let HIok : heap_iface_ok L SCFG HI := HI0_ok_closed sptop SCFG sc_alloc_cfg0.
Let TLY : L5TOP.toplay L := L0_toplay sptop W.
Lemma KB0 : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_overhead L. Proof. exact (L5TOPB.KPOS L TLY). Qed.
Let KPOS : 0 <= hl_k_per_malloc L := proj1 KB0.
Let BPOS : 0 <= hl_b_overhead L := proj2 KB0.
Let RESIZE : L5CS.resize_spec L HI := L5RSZ.resize_ok L HI LY HIok.
Let ASSIGN : L5CS.assign_spec L HI := L5ASG.assign_ok L HI LY HIok.
Let OPDELS : L5CS.opdel_sized_spec L HI := L5DEL.opdel_sized_ok L HI LY HIok.
Let COPYA : L5CS.copya_spec L HI := L5TOPB.COPYA L HI LY HIok.
Let HUGE : L5DS.resize_huge_spec := L5TOPB.RESIZE_HUGE.
Let CMP : L5CMP.cmp_spec := L5CMP.cmp_ok.
Let SHRS : L5SHR.shr_spec := L5SHR.shr_ok.
Let RED : L5RED.reduce_spec := L5REDG.reduce_ok.
Let DIVLOOP : L5DIVP.divloop_run_stmt := L5DIVLOOP.divloop_run.
Lemma DIVTAIL : L5DIVP.divtail_stmt L HI. Proof. pose proof OPDELS. apply (L5DIVTAIL.divtail_ok L HI LY HIok); assumption. Qed.
Lemma DIVTAIL2 : L5DIVTAIL.divtail2_stmt L HI. Proof. pose proof OPDELS. apply (L5DIVTAIL.divtail2_ok L HI LY HIok); assumption. Qed.
Lemma DIVN : L5DS.divN_spec L HI.
Proof.
  pose proof KPOS. pose proof BPOS. pose proof COPYA. pose proof ASSIGN. pose proof RESIZE. pose proof OPDELS. pose proof HUGE.
  pose proof DIVLOOP. pose proof DIVTAIL. pose proof CMP. apply (L5DIVNOKI.divN_ok L HI LY HIok); assumption.
Qed.
Lemma DIVEQ : L5DS.diveq_spec L HI. Proof. pose proof DIVN. pose proof OPDELS. apply (L5DIVEQ.diveq_ok L HI LY HIok); assumption. Qed.
Lemma SHRZ : L5DS.shrz_spec L HI. Proof. pose proof RESIZE. apply (L5SHRZ.shrz_ok L HI LY HIok); assumption. Qed.
Lemma UNNORM : L5DS.unnorm_spec L HI.
Proof. pose proof KPOS. pose proof BPOS. pose proof DIVEQ. pose proof SHRZ. pose proof SHRS. pose proof RED. apply (L5UNNORM.unnorm_ok L HI LY HIok); assumption. Qed.
Lemma NORM : L5NORM.norm_spec L HI. Proof. pose proof RESIZE. apply (L5NORMOK.norm_ok L HI LY HIok); assumption. Qed.
Lemma O1 : L5TOPB.OPMOD1_TAIL L HI.
Proof. pose proof KPOS. pose proof BPOS. pose proof COPYA. pose proof ASSIGN. pose proof RESIZE. pose proof OPDELS. pose proof UNNORM. pose proof DIVLOOP.
  apply (L5OPMOD1.opmod1_ok L HI LY HIok); assumption. Qed.
Lemma O2 : L5DS.opmod2_spec L HI.
Proof. pose proof KPOS. pose proof BPOS. pose proof COPYA. pose proof ASSIGN. pose proof RESIZE. pose proof OPDELS. pose proof UNNORM. pose proof DIVLOOP.
  apply (L5OPMOD2.opmod2_ok L HI LY HIok); assumption. Qed.
End Src0.

(* [comment removed for export] *)
Lemma OPMOD1_src0_ok : OPMOD1_src0. Proof. exact O1. Qed.
Lemma OPMOD2_src0_ok : OPMOD2_src0. Proof. exact O2. Qed.

