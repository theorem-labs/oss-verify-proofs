(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout Contract ContractDrv ContractS ReachInv ReachSlot.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import TobjJV FuzzOneIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Import Init.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Top OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Drv_spine OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_fuzz__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_free_top OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_calloc__G1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_mdirect__G4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_mslow__G4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_aslot__G11 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_X1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_X3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_XS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_mdirect_S OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Mal_malloc__G4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma asi_P : P.Mal_mslow__G4.Mal_mslow_top.asi_stmt. Proof. exact alloc_slot_init_asi. Qed.
Lemma asr_P : P.Mal_mslow__G4.Mal_mslow_top.asr_stmt. Proof. exact alloc_slot_reach. Qed.
Lemma MS_P : ContractMK.malloc_slow_TRK_P. Proof. exact (P.Mal_mslow__G4.Mal_mslow_top.malloc_slow_TRK_P_closed asi_P asr_P). Qed.
Lemma AS_P : ContractASK.alloc_slot_TRK_P. Proof. exact P.Mal_aslot__G11.Mal_aslot_JC.alloc_slot_TRK_P_closed. Qed.

Lemma MCs_P : malloc_contracts segsP C_P EC_P.
Proof.
  constructor.
  - exact P.Mal_malloc__G4.Mal_malloc_top.malloc_contract_P_closed.
  - exact (P.Mal_calloc__G1.Mal_calloc_contract.calloc_contract_P P.Mal_malloc__G4.Mal_malloc_top.malloc_contract_P_closed).
  - exact Mal_free_top.free_contract_P_ok.
Qed.
Lemma MCX_P : malloc_contracts_ex segsP C_P EC_P.
Proof.
  constructor.
  - exact P.Mal_malloc__G4.Mal_malloc_top.malloc_contract_ex_P_closed.
  - exact (P.Mal_calloc__G1.Mal_calloc_contract.calloc_contract_ex_P P.Mal_malloc__G4.Mal_malloc_top.malloc_contract_ex_P_closed).
  - exact Mal_free_top.free_contract_ex_P_ok.
Qed.
Lemma MIC_P : malloc_init_contract_P. Proof. exact P.Mal_malloc__G4.Mal_malloc_top.malloc_init_contract_P_closed. Qed.
(* [comment removed for export] *)
Lemma MIX_P : malloc_init_ex_P true. Proof. exact (Mal_X1.malloc_init_ex_true_of MS_P AS_P). Qed.
Lemma MBX_P : malloc_big_ex_P true. Proof. exact P.Mal_mdirect__G4.Mal_mdirect_DX.malloc_big_ex_true_closed. Qed.
Lemma FDX_P : free_drv_ex_P. Proof. exact Mal_free_top.free_drv_ex_P_ok. Qed.
Lemma MPX_P : malloc_payload_ex_P true.
Proof. exact (Mal_X3.malloc_payload_ex_true_of MS_P AS_P P.Mal_mdirect__G4.Mal_mdirect_X3.malloc_direct_ok_P). Qed.
(* [comment removed for export] *)
Lemma MIS_P : malloc_init_S_P. Proof. exact (Mal_XS.malloc_init_S_of MS_P AS_P). Qed.
Lemma MBS_P : malloc_big_S_P. Proof. exact Mal_mdirect_S.malloc_big_S_P_closed. Qed.
Lemma FDS_P : free_drv_S_P. Proof. exact Mal_free_top.free_drv_S_P_ok. Qed.
Lemma MPS_P : malloc_payload_S_P. Proof. exact (Mal_XS.malloc_payload_S_of MS_P AS_P). Qed.
Lemma FCX_P : free_contract_ex_P. Proof. exact Mal_free_top.free_contract_ex_P_ok. Qed.

(* [comment removed for export] *)
Lemma FS_P : fuzz_one_sum_stmt_P. Proof. exact (P.Lib_fuzz__G1.Lib_fuzz_one_top.fuzz_one_P MCs_P). Qed.
Lemma FSX_P : fuzz_one_sum_ex_stmt_P. Proof. exact (P.Lib_fuzz__G1.Lib_fuzz_one_top.fuzz_one_ex_P MCX_P). Qed.

Lemma lim_P : 2 ^ 30 <= source_alloc_limit <= 2 ^ 40. Proof. unfold source_alloc_limit. cbn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem top_closed_P_lim : forall lim, 2 ^ 30 <= lim <= 2 ^ 40 -> forall sp brk mb draw inp,
  valid_entry48 imgP (mkEntry sp brk mb draw) inp -> valid_input_either inp ->
  SOUND segsP (c0P sp brk mb draw lim inp) (Spec inp) /\
  COMPLETE segsP (c0P sp brk mb draw lim inp) (Spec inp) /\
  ~ reaches_error_a segsP (c0P sp brk mb draw lim inp).
Proof.
  intros lim Hlim sp brk mb draw inp Hent Hinp.
  apply (Top.top_P sp brk mb draw lim inp Hent Hinp).
  - exact (Drv_spine.spine_safe sp brk mb draw lim inp Hent Hinp MCs_P MIS_P MBS_P FDS_P MPS_P FS_P Hlim).
  - exact (Drv_spine.spine_ex sp brk mb draw lim inp Hent Hinp MIX_P MBX_P FDX_P MPX_P FCX_P FSX_P Hlim).
Qed.

Theorem top_closed_P : forall sp brk mb draw inp,
  valid_entry48 imgP (mkEntry sp brk mb draw) inp -> valid_input_either inp ->
  SOUND segsP (c0P sp brk mb draw source_alloc_limit inp) (Spec inp) /\
  COMPLETE segsP (c0P sp brk mb draw source_alloc_limit inp) (Spec inp) /\
  ~ reaches_error_a segsP (c0P sp brk mb draw source_alloc_limit inp).
Proof. exact (top_closed_P_lim source_alloc_limit lim_P). Qed.

Lemma lim_P_sanitizer : 2 ^ 30 <= LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source <= 2 ^ 40.
Proof. unfold LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source, LinuxProcessSemantics.EquivalenceDefinition.Equivalence.sanitizer_source_limit. cbn. lia. Qed.

(* [comment removed for export] *)
Theorem top_closed_P_sanitizer : forall sp brk mb draw inp,
  valid_entry48 imgP (mkEntry sp brk mb draw) inp -> valid_input_either inp ->
  SOUND segsP (c0P sp brk mb draw LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source inp) (Spec inp) /\
  COMPLETE segsP (c0P sp brk mb draw LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source inp) (Spec inp) /\
  ~ reaches_error_a segsP (c0P sp brk mb draw LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source inp).
Proof. exact (top_closed_P_lim _ lim_P_sanitizer). Qed.
