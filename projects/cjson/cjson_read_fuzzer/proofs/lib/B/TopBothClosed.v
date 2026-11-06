(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require TopUbsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_fuzz_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_traces.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_fuzz_top.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pv_common.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_pvalue_N2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Drv_iface2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Drv_traces.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Drv_stmt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require DrvTop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require DrvClosed.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AMainEntry.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AMainGlue.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ATop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_quarantine_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_quarantine_iface2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_init4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AInst.
Module TopBoth.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.TopUbsan.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_fuzz_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_traces OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_fuzz_top OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pv_common OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_pvalue_N2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Drv_iface2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Drv_traces OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.Drv_stmt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.DrvTop OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.DrvClosed OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AMainEntry OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AMainGlue OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ATop OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_quarantine_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_quarantine_iface2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_init4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AInst.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition DRV_NP : Z := 4 * FUZZ_NP (2^26).
Lemma DRV_NP_nonneg : 0 <= DRV_NP.
Proof. unfold DRV_NP, FUZZ_NP. lia. Qed.

Section TinvInstance.
  Variable S_LIB : list (list Z).
  Hypothesis HK : Z.of_nat (length (S_DRIVER ++ S_LIB)) + DRV_NP + 1 <= DEPOT_KMAX.
  Definition DTI : trs_iface := mk_tinv (S_DRIVER ++ S_LIB) DRV_NP HK DRV_NP_nonneg.
  Lemma DTI_init : TINV DTI 0 [].
  Proof. apply mk_tinv_TINV_init. Qed.
  Lemma DTI_drv : drv_traces_ok DTI.
  Proof. unfold drv_traces_ok. intros tr H. apply (proj2 (mk_tinv_STAT _ _ _ _ tr)). apply in_or_app. left. exact H. Qed.
  Lemma DTI_lib : forall tr, In tr S_LIB -> STAT DTI tr.
  Proof. intros tr H. apply (proj2 (mk_tinv_STAT _ _ _ _ tr)). apply in_or_app. right. exact H. Qed.
  Lemma DTI_np : 4 * FUZZ_NP (2^26) <= NPMAX DTI.
  Proof. unfold DTI, mk_tinv. cbn [NPMAX]. unfold DRV_NP. lia. Qed.
End TinvInstance.

Lemma HK_lib : Z.of_nat (length (S_DRIVER ++ CJ_traces.S_LIB)) + DRV_NP + 1 <= DEPOT_KMAX.
Proof. rewrite length_app, Nat2Z.inj_add, S_LIB_length. unfold DRV_NP, FUZZ_NP, DEPOT_KMAX. cbn. lia. Qed.

(* [comment removed for export] *)
Theorem a_main_stmt_open :
  (forall ACEIL : Ceil, @refill_spec ACEIL) -> (forall ACEIL : Ceil, @quarantine_put_spec2 ACEIL) -> a_main_stmt.
Proof.
  intros RF QP. apply a_main_stmt_of. intros ACEIL.
  exists (AINST (RF ACEIL) (QP ACEIL)), (DI (RF ACEIL) (QP ACEIL)). split.
  - exact (ARTI_inst (RF ACEIL) (QP ACEIL)).
  - apply (a_main_closed04 _ _ (DTI CJ_traces.S_LIB HK_lib) CJ_traces.S_LIB
             (DTI_init _ HK_lib) (DTI_drv _ HK_lib) (DTI_lib _ HK_lib) (DTI_np _ HK_lib)).
    exact (llvmfuzz_closed _ _ (FLAGLOW_inst (RF ACEIL) (QP ACEIL)) (SSPW_inst (RF ACEIL) (QP ACEIL))).
Qed.

Theorem both_base_open :
  (forall ACEIL : Ceil, @refill_spec ACEIL) -> (forall ACEIL : Ceil, @quarantine_put_spec2 ACEIL) ->
  strong_universal_error_free_T_scfg (alloc_only_cfg false) TopUbsan.SRC0 ATop.BOTH.
Proof. intros RF QP. exact (both_base_of (a_main_stmt_open RF QP)). Qed.

Theorem both_base_open_budgets :
  (forall ACEIL : Ceil, @refill_spec ACEIL) -> (forall ACEIL : Ceil, @quarantine_put_spec2 ACEIL) ->
  strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) source_alloc_limit target_alloc_limit TopUbsan.SRC0 ATop.BOTH.
Proof. intros RF QP. exact (both_base_of_budgets (a_main_stmt_open RF QP)). Qed.
End TopBoth.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import TopUbsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import ATop.
Import TopBoth.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_p_refillX RTW_q_top.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem both_base : strong_universal_error_free_T_scfg (alloc_only_cfg false) TopUbsan.SRC0 ATop.BOTH.
Proof. exact (both_base_open (@RTW_p_refillX.refill_proof) (@RTW_q_top.quarantine_put_closed)). Qed.

Theorem both_base_budgets :
  strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) source_alloc_limit target_alloc_limit TopUbsan.SRC0 ATop.BOTH.
Proof. exact (both_base_open_budgets (@RTW_p_refillX.refill_proof) (@RTW_q_top.quarantine_put_closed)). Qed.

(* [comment removed for export] *)
Theorem both_base_san :
  strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) sanitizer_source_limit target_alloc_limit TopUbsan.SRC0 ATop.BOTH.
Proof. exact (both_base_of_san (a_main_stmt_open (@RTW_p_refillX.refill_proof) (@RTW_q_top.quarantine_put_closed))). Qed.
