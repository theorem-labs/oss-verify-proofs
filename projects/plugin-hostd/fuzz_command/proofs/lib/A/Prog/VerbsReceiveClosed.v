(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closing pattern of the statement-pass re-fit for verbs_receive's ASan
   walk (lib/A/Prog/verbs_receive_top.v, tverbs_receive) at the pinned image (lib/A/Prog/CmdImg.v's instance PB_cmd,
   whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head), as SupRemoveAllRefitClosed.v does. The
   record hypotheses come from the A kit (CmdRecImg.v, CmdRecRest.v): IMG is cmd_img_facts_tfib, TL is cmd_palib,
   TLF is cmd_palibf, ML is cmd_model_laws, SIGP is cmd_sig_prog_PB, VOBJS / VHIS are cmd_val_objs_PB /
   cmd_val_his_PB, PRW is cmd_prw_tfib, SMP is cmd_stack_malloc_progress, ASF is cmd_astack_free_law and FFL is
   cmd_frame_flag_law (LAWS is the core's AR_laws_ok, inside verbs_receive_top.v). What remains is the statement's own
   hypotheses (the callees' contracts and the runtime entries), HB, MTL and MTFL. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString RtNumber RtAlloc04 RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c verbs_receive_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require verbs_receive_top.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(** * tverbs_receive at the pinned image *)
Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PB_cmd).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
Variables PC_STRDUP_RA0 PC_STRNDUP_RA0 : Z.
(* the allocator record and the meter's laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTFL : YC5d.ameter_fs_laws MT.
Theorem tverbs_receive_closed
  (TDESCRIPTORS_ADD : forall fx0 : YK11.FPState, descriptors_add_c.tdescriptors_add_spec (fx := fx0) B MT)
  (TDESCRIPTORS_GET : forall fx0 : YK11.FPState, descriptors_get_c.tdescriptors_get_spec (fx := fx0) B MT)
  (TDESCRIPTORS_PANEL_GET : forall fx0 : YK11.FPState,
     descriptors_panel_get_c.tdescriptors_panel_get_spec (fx := fx0) B MT)
  (TIS_INSTANCE_VERB : forall fx0 : YK11.FPState, is_instance_verb_c.tis_instance_verb_spec (fx := fx0) B MT)
  (TLV2_REFUSALS_FORGET : forall fx0 : YK11.FPState,
     lv2_refusals_forget_c.tlv2_refusals_forget_spec (fx := fx0) B MT)
  (TNUMBER : forall fx0 : YK11.FPState, number_c.tnumber_spec (fx := fx0) B MT)
  (TPINS_CLEAR : forall fx0 : YK11.FPState, pins_clear_c.tpins_clear_spec (fx := fx0) B MT)
  (TREPLY : forall fx0 : YK11.FPState, reply_c.treply_spec (fx := fx0) B MT)
  (TSUP_ADD : forall fx0 : YK11.FPState, sup_add_c.tsup_add_spec (fx := fx0) B MT)
  (TSUP_AFTER_REPLY : forall fx0 : YK11.FPState, sup_after_reply_c.tsup_after_reply_spec (fx := fx0) B MT)
  (TSUP_BROADCAST : forall fx0 : YK11.FPState, sup_broadcast_c.tsup_broadcast_spec (fx := fx0) B MT)
  (TSUP_CALL : forall fx0 : YK11.FPState, sup_call_c.tsup_call_spec (fx := fx0) B MT)
  (TSUP_CHAIN_CLEAR : forall fx0 : YK11.FPState, sup_chain_clear_c.tsup_chain_clear_spec (fx := fx0) B MT)
  (TSUP_CONNECT : forall fx0 : YK11.FPState, sup_connect_c.tsup_connect_spec (fx := fx0) B MT)
  (TSUP_HOST_SETTING : forall fx0 : YK11.FPState, sup_host_setting_c.tsup_host_setting_spec (fx := fx0) B MT)
  (TSUP_INSTANCE_INFO : forall fx0 : YK11.FPState, sup_instance_info_c.tsup_instance_info_spec (fx := fx0) B MT)
  (TSUP_INSTANCE_VERB : forall fx0 : YK11.FPState, sup_instance_verb_c.tsup_instance_verb_spec (fx := fx0) B MT)
  (TSUP_LV2_WORKER_SET : forall fx0 : YK11.FPState,
     sup_lv2_worker_set_c.tsup_lv2_worker_set_spec (fx := fx0) B MT)
  (TSUP_PIN_ACCEPT : forall fx0 : YK11.FPState, sup_pin_accept_c.tsup_pin_accept_spec (fx := fx0) B MT)
  (TSUP_POLICY_SET : forall fx0 : YK11.FPState, sup_policy_set_c.tsup_policy_set_spec (fx := fx0) B MT)
  (TSUP_POOL_CONFIG : forall fx0 : YK11.FPState, sup_pool_config_c.tsup_pool_config_spec (fx := fx0) B MT)
  (TSUP_QUARANTINE_CLEAR : forall fx0 : YK11.FPState,
     sup_quarantine_clear_c.tsup_quarantine_clear_spec (fx := fx0) B MT)
  (TSUP_REMOVE : forall fx0 : YK11.FPState, sup_remove_c.tsup_remove_spec (fx := fx0) B MT)
  (TSUP_REMOVE_ALL : forall fx0 : YK11.FPState, sup_remove_all_c.tsup_remove_all_spec (fx := fx0) B MT)
  (TSUP_REPLY_CODE : forall fx0 : YK11.FPState, sup_reply_code_c.tsup_reply_code_spec (fx := fx0) B MT)
  (TSUP_RESET : forall fx0 : YK11.FPState, sup_reset_c.tsup_reset_spec (fx := fx0) B MT)
  (TSUP_RESP : forall fx0 : YK11.FPState, sup_resp_c.tsup_resp_spec (fx := fx0) B MT)
  (TSUP_WORKER_ENV : forall fx0 : YK11.FPState, sup_worker_env_c.tsup_worker_env_spec (fx := fx0) B MT)
  (TSUP_WORKER_LIST : forall fx0 : YK11.FPState, sup_worker_list_c.tsup_worker_list_spec (fx := fx0) B MT)
  (TVERB_IS : forall fx0 : YK11.FPState, verb_is_c.tverb_is_spec (fx := fx0) B MT)
  (TCHAIN_WORDS : forall fx0 : YK11.FPState, chain_words_c.tchain_words_spec (fx := fx0) B MT)
  (TPIN_SET_WORDS : forall fx0 : YK11.FPState, pin_set_words_c.tpin_set_words_spec (fx := fx0) B MT)
  (SM4 : forall fx0 : YK11.FPState, astack_malloc_realizes (fx := fx0) SEGS B 4)
  (SH00 : forall fx0 : YK11.FPState, RtShadow.aset_shadow_realizes (fx := fx0) SEGS B (SIGMA CS___asan_set_shadow_00) 0)
  (SHF5 : forall fx0 : YK11.FPState,
     RtShadow.aset_shadow_realizes (fx := fx0) SEGS B (SIGMA CS___asan_set_shadow_f5) 0xf5)
  (SHF8 : forall fx0 : YK11.FPState,
     RtShadow.aset_shadow_realizes (fx := fx0) SEGS B (SIGMA CS___asan_set_shadow_f8) 0xf8)
  (STRLEN : forall fx0 : YK11.FPState,
     RtString.astrlen_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_strlen))
  (STRCMP : forall fx0 : YK11.FPState,
     RtString.astrcmp_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_strcmp))
  (STRNCMP : forall fx0 : YK11.FPState,
     RtString.astrncmp_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_strncmp))
  (STRCSPN : forall fx0 : YK11.FPState,
     RtString.astrcspn_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8)
  (STRTOK_R : forall fx0 : YK11.FPState,
     RtString.astrtok_r_realizes (fx := fx0) SEGS B (SIGMA CS_strtok_r) 0xa7098 0x6045d8)
  (AATOI : forall fx0 : YK11.FPState,
     RtNumber.aatoi_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8)
  (ASTRDUP : forall fx0 : YK11.FPState,
     RtAlloc04.astrdup04_rule (fx := fx0) SEGS B MT (SIGMA CS___interceptor_trampoline_strdup) PC_STRDUP_RA0)
  (ASTRNDUP : forall fx0 : YK11.FPState,
     RtAlloc04.astrndup04_rule (fx := fx0) SEGS B MT (SIGMA CS___interceptor_trampoline_strndup) PC_STRNDUP_RA0)
  (AFREE : forall fx0 : YK11.FPState, YC5d.afree04_rule (fx := fx0) SEGS B MT) :
  verbs_receive_c.tverbs_receive_spec B MT.
Proof.
exact (verbs_receive_top.tverbs_receive B MT PC_STRDUP_RA0 PC_STRNDUP_RA0
  TDESCRIPTORS_ADD TDESCRIPTORS_GET TDESCRIPTORS_PANEL_GET TIS_INSTANCE_VERB TLV2_REFUSALS_FORGET TNUMBER TPINS_CLEAR
  TREPLY TSUP_ADD TSUP_AFTER_REPLY TSUP_BROADCAST TSUP_CALL TSUP_CHAIN_CLEAR TSUP_CONNECT TSUP_HOST_SETTING
  TSUP_INSTANCE_INFO TSUP_INSTANCE_VERB TSUP_LV2_WORKER_SET TSUP_PIN_ACCEPT TSUP_POLICY_SET TSUP_POOL_CONFIG
  TSUP_QUARANTINE_CLEAR TSUP_REMOVE TSUP_REMOVE_ALL TSUP_REPLY_CODE TSUP_RESET TSUP_RESP TSUP_WORKER_ENV
  TSUP_WORKER_LIST TVERB_IS TCHAIN_WORDS TPIN_SET_WORDS
  SM4 (CmdRecRest.cmd_stack_malloc_progress B) (CmdRecRest.cmd_astack_free_law B) (CmdRecRest.cmd_frame_flag_law B)
  SH00 SHF5 SHF8 STRLEN STRCMP STRNCMP STRCSPN STRTOK_R AATOI ASTRDUP ASTRNDUP AFREE
  HB (CmdRecImg.cmd_img_facts_tfib B HB) (CmdRecRest.cmd_palib B HB) (CmdRecRest.cmd_palibf B HB)
  (CmdRecRest.cmd_model_laws B HB) MTL MTFL CmdRecRest.cmd_val_objs_PB CmdRecRest.cmd_val_his_PB
  CmdRecRest.cmd_sig_prog_PB (CmdRecRest.cmd_prw_tfib B HB)).
Qed.
End closed.
