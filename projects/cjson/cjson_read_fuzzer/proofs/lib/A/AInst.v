(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep CJ_iface RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_pop.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_pop.RT_artP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstate.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstate.RT_artR.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_quarantine_iface RTW_quarantine_iface2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_unwind.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_unwind.RTW_leaves_tiny.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_unwind.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_unwind.RTW_leaves_thread.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_leaves_rz RTW_leaves_ia RTW_unwind RTW_depot_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require DInst.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.DInst.RTW_sec_allocW.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_aspec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_q_wf2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_q_wf2.RTW_m_calloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_asec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_mallocN.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_alloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_mallocN.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_realloc0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_realloc0.RTW_m_free0.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_realloc0.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_realloc0.RTW_m_free.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_realloc0 RTW_m_realloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_unwind.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_unwind.RTW_fs_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_p_nn RT_drv DInst RT_init4 Drv_iface2 AMainEntry AMainGlue CJ_pv_common CJ_pvalue_N2.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CeilWrap.
Context {ACEIL : Ceil}.

Section INST.
  (* [comment removed for export] *)
  Hypothesis refill_proof : refill_spec.
  Hypothesis qput_proof : quarantine_put_spec2.

  (* [comment removed for export] *)
  Definition depot_ok : depot_put_specS := depot_put_proof'.
  Definition unwind_ok : unwind_spec := unwind_proof.
  Definition alloc_sec_ok : alloc_sec_stmt := alloc_sec_proof depot_ok poison_shadow_ok.
  Definition combined_ok : combined_alloc_spec := combined_alloc_proof refill_proof large_alloc_proofW.
  Definition allocate_ok : allocate_spec :=
    allocate_proof combined_ok depot_ok poison_shadow_ok asan_inited_proof rss_exceeded_proof rzsize2log_proof
                   get_current_thread_proof set_oom_proof may_return_null_proof alloc_sec_ok.

  (* [comment removed for export] *)
  Definition art_malloc_ok : malloc_lscps_stmt ARTd :=
    art_malloc_proof try_asan_init_proof get_malloc_ctx_size_proof get_current_pc_proof set_errno_enomem_proof unwind_ok allocate_ok.
  Definition art_free_ok : free_lscps_stmt ARTd :=
    art_free_proof internal_allocator_proof get_malloc_ctx_size_proof get_current_pc_proof unwind_ok depot_ok qput_proof.
  Definition art_free_null_ok : free_null_lscps_stmt ARTd :=
    art_free_null_proof internal_allocator_proof get_malloc_ctx_size_proof get_current_pc_proof unwind_ok.
  Definition art_realloc_ok : realloc_lscps_stmt ARTd :=
    art_realloc_proof try_asan_init_proof internal_allocator_proof get_malloc_ctx_size_proof get_current_pc_proof get_thread_stats_proof
                      set_errno_enomem_proof unwind_ok allocate_ok depot_ok qput_proof.
  Definition art_realloc_null_ok : realloc_null_lscps_stmt ARTd :=
    art_realloc_null_proof try_asan_init_proof internal_allocator_proof get_malloc_ctx_size_proof get_current_pc_proof
                           set_errno_enomem_proof unwind_ok allocate_ok.

  (* [comment removed for export] *)
  Definition AINST : art_iface :=
    mkARTI ARTd artd_binv artd_frame artd_perm artd_lower artd_block_range artd_blocks_disjoint artd_nodup artd_block_wr
           artd_block_slack artd_shadow artd_frame_facts artd_flag_high artd_frames_disjoint artd_ff_release artd_global_shadow
           artd_cjst artd_ssp artd_rtcells artd_lowshadow artd_model_frame
           art_malloc_ok art_free_ok art_free_null_ok art_realloc_ok art_realloc_null_ok art_stkmalloc1_proof art_stkmalloc2_proof
           artd_block_band artd_frame_band.

  (* [comment removed for export] *)
  Definition DI : drv_iface2 AINST :=
    DInst.DINST AINST eq_refl try_asan_init_proof get_malloc_ctx_size_proof get_current_pc_proof internal_allocator_proof
                asan_inited_proof rss_exceeded_proof rzsize2log_proof get_current_thread_proof unwind_ok depot_ok
                refill_nn_proof qput_proof.

  (* [comment removed for export] *)
  Definition FLAGLOW_inst : art_flag_low_stmt AINST := artd_flag_low.
  Definition SSPW_inst : sspw_stmt AINST := artd_sspw.

  (* [comment removed for export] *)
  Definition ARTI_inst : art_init_stmt AINST DI := art_init_closed.
End INST.
End CeilWrap.
