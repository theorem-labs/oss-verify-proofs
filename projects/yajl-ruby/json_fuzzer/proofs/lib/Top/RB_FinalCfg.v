(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit.
Require LinuxProcessSemantics.EquivalenceDefinition.FinInput.
Require LinuxProcessSemantics.EquivalenceDefinition.Classifier.
Require LinuxProcessSemantics.EquivalenceDefinition.Measure.
Require LinuxProcessSemantics.EquivalenceDefinition.PatchClassifySpec.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
Require OSSVerify.yajl_ruby.json_fuzzer.images.Plain.
Require OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr Nodes NodesCfg InitMem RunInit Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim StdioBase Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanBudget2 AsanDepot AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import
  B_base B_alloc_iface B_iface B_iface5x BF_unwind BF_fakestack_rep B_live B_policy5 B_budget5 B_slack5 B_bundle B_benv5 B_init5 B_instD5 B_inst5 BDrv_ctx BDrv_A BDrv_E
  BF_alloc_iface BF_free_iface BF_mallocT2 BF_reallocT BF_freeT2 BF_dput_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import SpecT GlueCfg RunInitCfg R_TopCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require RB_EquivCfg RU_FinalCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Clf Require ClfTop.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.TopB Require B_MainMS B_TopCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require BF_deallocT2 BF_deallocT3 BF_deallocT5 BF_deallocT7 BF_dputT BF_qrep BF_caframe BF_allocT5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require B_MainReach5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

(* [comment removed for export] *)
Section BHyps.
  Context {RC__ : RunCeiling}.
  Lemma B_ALLOC : forall E0 FSB0 PL0 HR0 L0 RES0 EB0,
    env0_ok5 E0 -> pl0_ok5 E0 PL0 -> Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192 -> 0 <= EB0 <= 2^32 ->
    zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096 -> gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat ->
    l0_ok5 E0 L0 RES0 ->
    allocate_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.
  Proof.
    intros E0 FSB0 PL0 HR0 L0 RES0 EB0 ENV0 PL0OK HR0_ok EB0_ok ENV_depot GW L0OK.
    exact (BF_allocT5.allocate_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 HR0_ok EB0_ok ENV_depot ENV0 PL0OK L0OK).
  Qed.
  Lemma B_R3 : forall E0, env0_ok5 E0 -> BF_deallocT3.R3_stmt E0.
  Proof.
    intros E0 ENV0. pose proof ENV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IC0 & _).
    exact (BF_qrep.R3_holds E0 IC0).
  Qed.
  Lemma B_RECYC : forall E0 FSB0 PL0 HR0 L0 RES0 EB0,
    env0_ok5 E0 -> pl0_ok5 E0 PL0 -> Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192 -> 0 <= EB0 <= 2^32 ->
    zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096 -> gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat ->
    l0_ok5 E0 L0 RES0 ->
    BF_deallocT5.recycle_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.
  Proof.
    intros E0 FSB0 PL0 HR0 L0 RES0 EB0 ENV0 PL0OK HR0_ok EB0_ok ENV_depot GW L0OK.
    exact (BF_deallocT7.recycle_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 HR0_ok ENV0 PL0OK L0OK).
  Qed.
  Lemma B_DEALLOC : forall E0 FSB0 PL0 HR0 L0 RES0 EB0,
    env0_ok5 E0 -> pl0_ok5 E0 PL0 -> Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192 -> 0 <= EB0 <= 2^32 ->
    zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096 -> gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat ->
    l0_ok5 E0 L0 RES0 ->
    dealloc_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.
  Proof.
    intros E0 FSB0 PL0 HR0 L0 RES0 EB0 ENV0 PL0OK HR0_ok EB0_ok ENV_depot GW L0OK.
    exact (BF_deallocT5.dealloc_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 HR0_ok EB0_ok ENV_depot ENV0 PL0OK L0OK
             (B_R3 E0 ENV0)
             (B_RECYC E0 FSB0 PL0 HR0 L0 RES0 EB0 ENV0 PL0OK HR0_ok EB0_ok ENV_depot GW L0OK)).
  Qed.
End BHyps.

Definition B_SPEC := B_TopCfg.B_realizes_spec_cfg B_MainReach5.b_main_reach (@B_ALLOC) (@B_DEALLOC).

Theorem strong_universal_error_free_json_fuzzer_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.AsanUbsan.M.phdrs).
Proof.
  (* [comment removed for export] *)
  exact (RB_EquivCfg.strong_universal_error_free_json_fuzzer_both_budgets RU_FinalCfg.R_realizes_spec_final_2G B_SPEC).
Qed.
