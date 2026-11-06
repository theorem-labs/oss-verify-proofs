(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import HeapIface LibIface L5Defs L5CoreSpecs L5CoreSpecsU
     L5DivSpecs L5DivSpecsU L5DivSpecsO L5DivSpecsOU L5OpMod2SpecU L5DivParts L5DivPartsU L5OpMod1Tail
     L5NormU L5NormOkU L5CmpU L5ShrU L5ReduceU L5ReduceGU
     L5ResizeU L5AssignU L5OpdelU
     L5ShrzU L5DivEqU L5UnnormU L5DivLoopU L5DivTailU L5DivNOkIU L5DivO2SU L5DivO2KU L5OpMod1U L5OpMod2U
     L5UnwindSpecs L5UnwindSpecsU L5TCopyU L5Top L5TopU L5Layout L5TopBind L5TopBindU
     BigintFinal BigintFinalA BigintBaseH BigintBaseHA BigintBaseS0.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import HeapInst0 HeapInst1 HeapClosed.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section Ub0.
Variable sptop : Z.
Hypothesis W : sptop_window sptop.
Let L := L1 sptop.
Let HI := HI1 sptop.
Let LY : L5CSU.layout L := L1_layout sptop.
Let HIok : heap_iface_ok L SCFG HI := HI1_ok_closed sptop SCFG sc_alloc_cfg0.
Let TLY : L5TOPU.toplay L := L1_toplay sptop W.
Lemma KB1 : 0 <= hl_k_per_malloc L /\ 0 <= hl_b_overhead L. Proof. exact (L5TOPBU.KPOS L TLY). Qed.
Let KPOS : 0 <= hl_k_per_malloc L := proj1 KB1.
Let BPOS : 0 <= hl_b_overhead L := proj2 KB1.
Let RESIZE : L5CSU.resize_spec L HI := L5RSZU.resize_ok L HI LY HIok.
Let ASSIGN : L5CSU.assign_spec L HI := L5ASGU.assign_ok L HI LY HIok.
Let OPDELS : L5CSU.opdel_sized_spec L HI := L5DELU.opdel_sized_ok L HI LY HIok.
Let COPYA : L5CSU.copya_spec L HI := L5TOPBU.COPYA L HI LY HIok.
Let COPYC : L5CSU.copy_spec L HI := L5TCPU.copy_ok L HI LY HIok.
Let HUGE : L5DSU.resize_huge_spec := L5TOPBU.RESIZE_HUGE.
Let CMP : L5CMPU.cmp_spec := L5CMPU.cmp_ok.
Let SHRS : L5SHRU.shr_spec := L5SHRU.shr_ok.
Let RED : L5REDU.reduce_spec := L5REDGU.reduce_ok.
Let DIVLOOP : L5DIVPU.divloop_run_stmt := L5DIVLOOPU.divloop_run.
Lemma DIVTAILU : L5DIVPU.divtail_stmt L HI. Proof. pose proof OPDELS. apply (L5DIVTAILU.divtail_ok L HI LY HIok); assumption. Qed.
Lemma DIVTAIL2U : L5DIVTAILU.divtail2_stmt L HI. Proof. pose proof OPDELS. apply (L5DIVTAILU.divtail2_ok L HI LY HIok); assumption. Qed.
Lemma DIVNU : L5DSU.divN_spec L HI.
Proof.
  pose proof KPOS. pose proof BPOS. pose proof COPYA. pose proof ASSIGN. pose proof RESIZE. pose proof OPDELS. pose proof HUGE.
  pose proof DIVLOOP. pose proof DIVTAILU. pose proof CMP. apply (L5DIVNOKIU.divN_ok L HI LY HIok); assumption.
Qed.
Lemma DIVEQU : L5DSU.diveq_spec L HI. Proof. pose proof DIVNU. pose proof OPDELS. apply (L5DIVEQU.diveq_ok L HI LY HIok); assumption. Qed.
Lemma SHRZU : L5DSU.shrz_spec L HI. Proof. pose proof RESIZE. apply (L5SHRZU.shrz_ok L HI LY HIok); assumption. Qed.
Lemma UNNORMU : L5DSU.unnorm_spec L HI.
Proof. pose proof KPOS. pose proof BPOS. pose proof DIVEQU. pose proof SHRZU. pose proof SHRS. pose proof RED. apply (L5UNNORMU.unnorm_ok L HI LY HIok); assumption. Qed.
Lemma NORMU : L5NORMU.norm_spec L HI. Proof. pose proof RESIZE. apply (L5NORMOKU.norm_ok L HI LY HIok); assumption. Qed.
Lemma DIVO2U : L5DO2SU.divO2_spec L HI.
Proof.
  pose proof KPOS. pose proof BPOS. pose proof COPYA. pose proof ASSIGN. pose proof RESIZE. pose proof OPDELS. pose proof NORMU. pose proof UNNORMU.
  pose proof DIVLOOP. pose proof DIVTAILU. pose proof DIVTAIL2U. pose proof CMP. apply (L5DIVO2KU.divO2_ok L HI LY HIok); assumption.
Qed.
Lemma O1U : L5TOPBU.OPMOD1_TAIL L HI.
Proof.
  pose proof KPOS. pose proof BPOS. pose proof COPYA. pose proof COPYC. pose proof ASSIGN. pose proof RESIZE. pose proof OPDELS. pose proof CMP.
  pose proof UNNORMU. pose proof NORMU. pose proof DIVLOOP. pose proof DIVTAILU. pose proof DIVTAIL2U. pose proof DIVNU. pose proof HUGE.
  apply (L5OPMOD1U.opmodf1_ok L HI LY HIok); assumption.
Qed.
Lemma O2U : L5OM2SU.opmodf2_spec L HI.
Proof.
  pose proof KPOS. pose proof BPOS. pose proof COPYA. pose proof COPYC. pose proof ASSIGN. pose proof RESIZE. pose proof OPDELS. pose proof CMP.
  pose proof UNNORMU. pose proof NORMU. pose proof DIVLOOP. pose proof DIVTAILU. pose proof DIVTAIL2U. pose proof DIVNU. pose proof HUGE. pose proof DIVO2U.
  apply (L5OPMOD2U.opmodf2_ok L HI LY HIok); assumption.
Qed.
End Ub0.

(* [comment removed for export] *)
Lemma OPMOD1_ub0_ok : OPMOD1_ub0. Proof. exact O1U. Qed.
Lemma OPMOD2_ub0_ok : OPMOD2_ub0. Proof. exact O2U. Qed.

(* [comment removed for export] *)
Theorem fuzz_bigint_ubsan_base :
  strong_universal_error_free_T_scfg cfg0
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. exact (fuzz_bigint_ubsan_modulo_divide OPMOD1_src0_ok OPMOD2_src0_ok OPMOD1_ub0_ok OPMOD2_ub0_ok). Qed.

Theorem fuzz_bigint_ubsan_base_abort :
  strong_universal_error_free_T_scfg_budgets_abort cfg0 ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. exact (fuzz_bigint_ubsan_abort_modulo_divide OPMOD1_src0_ok OPMOD2_src0_ok OPMOD1_ub0_ok OPMOD2_ub0_ok). Qed.
