(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsDriverLaws BakeStackRep
  BS_InstDefs BS_InstLaws1 BS_InstLaws2 BS_InstLaws3 BS_InstStubs BS_InstHeap BS_InstFree RtB_Iface RtB_Ext RtB_Annot.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Inst.
  Context {HCEIL : HeapCeil}.
  Variable p : iparams.
  Hypothesis TRLEN : (length (ip_TR p) <= 1000)%nat.
  Hypothesis TROP : trace_ok (ip_TR p) APC0_MALLOC [ARA_OPNEW].

  Theorem inst_rt_hyps : asan_rt_hyps (KHp p).
  Proof.
    pose proof (inst_SR_laws p) as Lsr. pose proof (inst_MPRES_laws p) as Lmp.
    pose proof (inst_RHEAP_block_range p) as Lbr. pose proof (inst_RHEAP_fsb p) as Lfsb.
    pose proof (inst_rauxv_frame p) as Laux. pose proof (inst_chain_laws p) as Lch.
    pose proof (inst_TR_laws1 p TROP) as Ltr.
    pose proof (inst_RHEAP_frame p) as Lrf. pose proof (inst_malloc_stmt p TRLEN) as Lma.
    pose proof (inst_free_stmt p TRLEN) as Lfr. pose proof (inst_free_null_stmt p) as Lfn.
    unfold asan_rt_hyps.
    split; [exact Lsr|]. split; [exact (inst_AKREL_laws p)|]. split; [exact Lmp|].
    split; [exact (inst_alloc_ok_of_live p)|]. split; [exact (inst_cost_laws p)|].
    split; [exact Lrf|]. split; [exact Lbr|]. split; [exact (inst_RHEAP_blocks_disjoint p)|]. split; [exact (inst_RHEAP_blocks_nodup p)|].
    split; [exact (inst_RHEAP_shvis p)|]. split; [exact Lfsb|]. split; [exact (inst_RHEAP_thr p)|].
    split; [exact Laux|]. split; [exact (inst_lb_remove_laws p)|].
    split; [exact (inst_RFS_frame p)|]. split; [exact (inst_RFS_ext p)|]. split; [exact (inst_RFS_range p)|].
    split; [exact (inst_RFS_disjoint p)|]. split; [exact (inst_RFS_nodup p)|]. split; [exact (inst_RFS_shvis p)|].
    split; [exact (inst_frame_release p)|].
    split; [exact Lch|]. split; [exact Ltr|].
    split; [exact Lma|]. split; [exact (opnew_of_malloc _ Lsr Lmp Lbr Lfsb Lrf Laux Lch Ltr Lma)|].
    split; [exact Lfr|]. split; [exact (opdel_of_free _ Lsr Lmp Lfr)|]. split; [exact (opdel2_of_free _ Lsr Lmp Lfr)|].
    split; [exact Lfn|]. split; [exact (opdel_null_of_free_null _ Lsr Lmp Lfn)|]. split; [exact (opdel2_null_of_free_null _ Lsr Lmp Lfn)|].
    split; [exact (inst_stack_malloc_1 p)|]. split; [exact (inst_stack_malloc_4 p)|]. split; [exact inst_set_shadow_f5|].
    split; [exact inst_asan_memcpy|]. split; [exact inst_asan_memset|]. split; [exact inst_asan_memmove|].
    split; [exact inst_memcpy_icpt|]. split; [exact inst_memmove_icpt|].
    split; [exact inst_strlen_icpt|]. split; [exact inst_strncmp_icpt|]. exact inst_annotate_cc.
  Qed.

  Theorem inst_rt_hyps_bp : asan_rt_hyps_bp (KHp p).
  Proof.
    split; [exact inst_rt_hyps|]. split; [apply rt_bp_ext_ok; intros LF m; cbn [as_RFS KHp as_FSB]; apply iff_refl|].
    split; [exact (inst_alloc_ok_of_live_bp p)|]. split; [exact (inst_RHEAP_ahm p)|].
    split; [exact annotate_gen_ok|].
    split; intros n; cbn [as_Cf as_Cm KHp]; unfold ICf, ICm, ICM; reflexivity.
  Qed.
End Inst.
