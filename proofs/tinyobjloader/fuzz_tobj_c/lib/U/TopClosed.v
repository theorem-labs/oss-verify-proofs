(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics MemImageType StackLayout Fs State Specs Run.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout Contract ContractDrv ContractS ReachInv ReachSlot.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import TobjJV FuzzOneIface.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import DriverSpec.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free_top OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_calloc__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mslow__G4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_aslot__G11 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_X1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_X3 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_XS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect_S OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G4.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Top OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Drv_spine.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1.S_lo OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1.lo_defs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1.lo_entry OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4.fz_pf.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1.lo_tail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L3.fs_all OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9.vr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9.aa OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8.vf OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11.fu.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1.lo_bd OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4.bd.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1.lo_loop OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5.hf.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma asi_U : U.Mal_mslow__G4.Mal_mslow_top.asi_stmt. Proof. exact alloc_slot_init_asi. Qed.
Lemma asr_U : U.Mal_mslow__G4.Mal_mslow_top.asr_stmt. Proof. exact alloc_slot_reach. Qed.
Lemma MS_U : ContractMK.malloc_slow_TRK_U. Proof. exact (U.Mal_mslow__G4.Mal_mslow_top.malloc_slow_TRK_P_closed asi_U asr_U). Qed.
Lemma AS_U : ContractASK.alloc_slot_TRK_U. Proof. exact U.Mal_aslot__G11.Mal_aslot_JC.alloc_slot_TRK_P_closed. Qed.

Lemma MCs_U : malloc_contracts segsU C_U EC_U.
Proof.
  constructor.
  - exact U.Mal_malloc__G4.Mal_malloc_top.malloc_contract_P_closed.
  - exact (U.Mal_calloc__G1.Mal_calloc_contract.calloc_contract_U U.Mal_malloc__G4.Mal_malloc_top.malloc_contract_P_closed).
  - exact U.Mal_free_top.free_contract_P_ok.
Qed.
Lemma MCX_U : malloc_contracts_ex segsU C_U EC_U.
Proof.
  constructor.
  - exact U.Mal_malloc__G4.Mal_malloc_top.malloc_contract_ex_P_closed.
  - exact (U.Mal_calloc__G1.Mal_calloc_contract.calloc_contract_ex_U U.Mal_malloc__G4.Mal_malloc_top.malloc_contract_ex_P_closed).
  - exact U.Mal_free_top.free_contract_ex_P_ok.
Qed.
Lemma MIC_U : malloc_init_contract_U. Proof. exact U.Mal_malloc__G4.Mal_malloc_top.malloc_init_contract_P_closed. Qed.
(* [comment removed for export] *)
Lemma MIX_U : malloc_init_ex_U true. Proof. exact (U.Mal_X1.malloc_init_ex_true_of MS_U AS_U). Qed.
Lemma MBX_U : malloc_big_ex_U true. Proof. exact U.Mal_mdirect__G4.Mal_mdirect_DX.malloc_big_ex_true_closed. Qed.
Lemma FDX_U : free_drv_ex_U. Proof. exact U.Mal_free_top.free_drv_ex_P_ok. Qed.
Lemma MPX_U : malloc_payload_ex_U true.
Proof. exact (U.Mal_X3.malloc_payload_ex_true_of MS_U AS_U U.Mal_mdirect__G4.Mal_mdirect_X3.malloc_direct_ok_P). Qed.
(* [comment removed for export] *)
Lemma MIS_U : malloc_init_S_U. Proof. exact (U.Mal_XS.malloc_init_S_of MS_U AS_U). Qed.
Lemma MBS_U : malloc_big_S_U. Proof. exact U.Mal_mdirect_S.malloc_big_S_P_closed. Qed.
Lemma FDS_U : free_drv_S_U. Proof. exact U.Mal_free_top.free_drv_S_P_ok. Qed.
Lemma MPS_U : malloc_payload_S_U. Proof. exact (U.Mal_XS.malloc_payload_S_of MS_U AS_U). Qed.
Lemma FCX_U : free_contract_ex_U. Proof. exact U.Mal_free_top.free_contract_ex_P_ok. Qed.

Lemma BD_U : U.L1.lo_entry.K_stmt U.L1.lo_defs.LoU.K_bd.
Proof. exact (U.L1.lo_bd.lo_bd_sum_U U.L4.bd.builder_dispose_sum_U). Qed.
Lemma BDX_U : U.L1.lo_entry.K_ex_stmt U.L1.lo_defs.LoU.K_bd.
Proof. exact (U.L1.lo_bd.lo_bd_sum_ex_U U.L4.bd.builder_dispose_sum_ex_U). Qed.

Lemma TAIL_U : U.L1.lo_entry.K_stmt U.L1.lo_defs.LoU.K_tail.
Proof. exact (U.L1.lo_tail.lo_tail_K_U U.L3.fs_all.fs_sum_closed U.L9.vr.vr_sum (U.L8.vf.vf_sum_U U.L9.aa.aa_sum) U.L11.fu.finalize_unknowns_sum_U BD_U). Qed.
Lemma TAILX_U : U.L1.lo_entry.K_ex_stmt U.L1.lo_defs.LoU.K_tail.
Proof. exact (U.L1.lo_tail.lo_tail_K_ex_U U.L3.fs_all.fs_ex_closed U.L9.vr.vr_sum_ex (U.L8.vf.vf_ex_U U.L9.aa.aa_sum_ex) U.L11.fu.finalize_unknowns_sum_ex_U BDX_U). Qed.

Lemma LOOP_U : U.L1.lo_entry.K_stmt U.L1.lo_defs.LoU.K_loop.
Proof. exact (U.L1.lo_loop.lo_loop_sum_U U.L5.hf.handle_f_sum_U TAIL_U BD_U). Qed.
Lemma LOOPX_U : U.L1.lo_entry.K_ex_stmt U.L1.lo_defs.LoU.K_loop.
Proof. exact (U.L1.lo_loop.lo_loop_sum_ex_U U.L5.hf.handle_f_sum_ex_U TAILX_U BDX_U). Qed.

Lemma LO_U : U.L1.S_lo.load_obj_stmt_U. Proof. exact (U.L1.lo_entry.load_obj_sum_U MCs_U LOOP_U TAIL_U BD_U). Qed.
Lemma LOX_U : U.L1.S_lo.load_obj_ex_stmt_U. Proof. exact (U.L1.lo_entry.load_obj_sum_ex_U MCX_U LOOPX_U TAILX_U BDX_U). Qed.

(* [comment removed for export] *)
Lemma FS_U : fuzz_one_sum_stmt_U. Proof. exact (U.L4.fz_pf.fuzz_one_U MCs_U LO_U). Qed.
Lemma FSX_U : fuzz_one_sum_ex_stmt_U. Proof. exact (U.L4.fz_pf.fuzz_one_ex_U MCX_U LOX_U). Qed.

Lemma lim_U : 2 ^ 30 <= target_alloc_limit <= 2 ^ 40. Proof. unfold target_alloc_limit. cbn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem top_closed_U_lim : forall lim, 2 ^ 30 <= lim <= 2 ^ 40 -> forall sp brk mb draw inp,
  valid_entry48 imgU (mkEntry sp brk mb draw) inp -> valid_input_either inp ->
  SOUND segsU (c0U sp brk mb draw lim inp) (Spec inp) /\
  COMPLETE segsU (c0U sp brk mb draw lim inp) (Spec inp) /\
  ~ reaches_error_a segsU (c0U sp brk mb draw lim inp).
Proof.
  intros lim Hlim sp brk mb draw inp Hent Hinp.
  apply (U.Top.top_U sp brk mb draw lim inp Hent Hinp).
  - exact (U.Drv_spine.spine_safe_U sp brk mb draw lim inp Hent Hinp MCs_U MIS_U MBS_U FDS_U MPS_U FS_U Hlim).
  - exact (U.Drv_spine.spine_ex_U sp brk mb draw lim inp Hent Hinp MIX_U MBX_U FDX_U MPX_U FCX_U FSX_U Hlim).
Qed.

Theorem top_closed_U : forall sp brk mb draw inp,
  valid_entry48 imgU (mkEntry sp brk mb draw) inp -> valid_input_either inp ->
  SOUND segsU (c0U sp brk mb draw target_alloc_limit inp) (Spec inp) /\
  COMPLETE segsU (c0U sp brk mb draw target_alloc_limit inp) (Spec inp) /\
  ~ reaches_error_a segsU (c0U sp brk mb draw target_alloc_limit inp).
Proof. exact (top_closed_U_lim target_alloc_limit lim_U). Qed.
