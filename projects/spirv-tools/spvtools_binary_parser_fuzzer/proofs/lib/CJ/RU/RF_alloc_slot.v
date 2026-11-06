(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocTree MallocFacts_A MallocHINV Malloc_fp MallocNat MallocFacts_AS ASlot_I ASlot_M0 MallocFacts_AM MallocFacts_AMP.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog CtxMono.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.RU Require Import RMallocRep RMallocTree RMalloc_fp RAllocSlot_iface RASlot_I RF_am_P RF_alloc_meta RASlot_M6.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require MallocFacts_inv4.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import AcLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Section AUXSEC.
Context {AUXM : auxv_mode}.

Lemma ras_pre2_intro : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> ras_pre2 st (set_tick t st) sc n FUEL.
Proof.
  intros st LB t sc n AR MF TT SC N FIT. split; [| split; [| split; [| repeat split; lia]]].
  - exists LB. split; [exact AR| apply ist_top; exact TT].
  - apply ER_refl_tick.
  - apply ALLC_tick; [| exact TT]. exact (mf_cell_ticks _ _ MF).
Qed.

Lemma IST_init1 st0 st : IST st0 st -> c_init_done (ctx st0) = 1 -> c_init_done (ctx st) = 1.
Proof.
  induction 1 as [t Ht| o st sc st1 st2 m H IH Hsc TF LF]; intros I0.
  - exact I0.
  - specialize (IH I0). unfold ta_fail, kS, bS in TF.
    pose proof (CtxMono.try_avail_ret_rel sc st st1 0 (fun x y => SRet (Some (x, y))) ltac:(intros; eexists; reflexivity) TF) as R1.
    assert (I1 : cinit st1 = 1) by (eapply CtxMono.REL_init1; [exact R1| exact IH]).
    destruct LF as (ans & o' & Hf). unfold mrun, kS, bS in Hf.
    pose proof (CtxMono.alloc_meta_leaf_init pans_mem pupd_mem o st1 ans (o', Some (st2, Some m)) (or_intror I1) Hf) as [I2 _].
    exact I2.
Qed.

Lemma ramp_as : RAMP_AS ram_pre.
Proof.
  intros st0 LB st sc st1 [AR IM] IS SC TF. split.
  - exact (MallocFacts_inv4.ist_ampre_proof st0 LB st sc st1 AR IS SC TF).
  - destruct IM as [I0|AV]; [left| right; exact AV].
    pose proof (IST_init1 st0 st IS I0) as I1. unfold ta_fail, kS, bS in TF.
    pose proof (CtxMono.try_avail_ret_rel sc st st1 0 (fun x y => SRet (Some (x, y))) ltac:(intros; eexists; reflexivity) TF) as R1.
    eapply CtxMono.REL_init1; [exact R1| exact I1].
Qed.

Theorem ralloc_slot_spec : ralloc_slot_stmt ras_pre2 as_inv2.
Proof.
  unfold ralloc_slot_stmt. intros fuel.
  exact (ralloc_slot_ok ram_pre ralloc_meta_spec ramp_as fuel).
Qed.

End AUXSEC.

End AC_1.
