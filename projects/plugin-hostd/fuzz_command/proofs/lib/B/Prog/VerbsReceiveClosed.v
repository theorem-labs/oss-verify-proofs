(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F, for verbs_receive on the
   ASan+UBSan build of plugin-hostd/fuzz_command (image B, entry 0x8ce4c): lib/B/Prog/verbs_receive_top.v's
   tverbs_receive with the per-binary record hypotheses it names discharged at the pinned image -- lib/B/Prog/CmdImg.v's
   instance PB_cmd, whose segments are tfibsegs (lib/B/YB1v.v), and the sink head YE2k.tfib_sink_head -- as A's
   SupRemoveAllRefitClosed.v does on the A side:
   - IMG is cmd_img_facts_tfib (CmdRecImg.v, by the closed checks of CmdRecImgChk.v);
   - TL is cmd_palib (CmdRecRest.v);
   - VOBJS, VHIS, SIGP are CmdObj.v's bridges for PB_cmd, cmd_val_objs_PB, cmd_val_his_PB, cmd_sig_prog_PB
     (CmdRecRest.v);
   - TLF is cmd_palibf, ML is cmd_model_laws, PRW is cmd_prw_tfib, SMP is cmd_stack_malloc_progress, ASF is
     cmd_astack_free_law and FFL is cmd_frame_flag_law (CmdRecRest.v).
   What remains is the statement's own hypotheses (the 32 callees' contracts and the runtime entries, at every FP
   state), the allocator record HB, and the laws of the meter (MTL, MTFL). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString RtNumber RtAlloc04 RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require verbs_receive_c verbs_receive_top.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PB_cmd).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
Variables PC_STRDUP_RA0 PC_STRNDUP_RA0 : Z.
(* the 32 program callees' contracts (verbs_receive_c.v:225-256), at every FP state *)
Hypothesis TCHAIN_WORDS : forall fx0 : YK11.FPState, tchain_words_spec (fx := fx0) B MT.
Hypothesis TDESCRIPTORS_ADD : forall fx0 : YK11.FPState, tdescriptors_add_spec (fx := fx0) B MT.
Hypothesis TDESCRIPTORS_GET : forall fx0 : YK11.FPState, tdescriptors_get_spec (fx := fx0) B MT.
Hypothesis TDESCRIPTORS_PANEL_GET : forall fx0 : YK11.FPState, tdescriptors_panel_get_spec (fx := fx0) B MT.
Hypothesis TIS_INSTANCE_VERB : forall fx0 : YK11.FPState, tis_instance_verb_spec (fx := fx0) B MT.
Hypothesis TLV2_REFUSALS_FORGET : forall fx0 : YK11.FPState, tlv2_refusals_forget_spec (fx := fx0) B MT.
Hypothesis TNUMBER : forall fx0 : YK11.FPState, tnumber_spec (fx := fx0) B MT.
Hypothesis TPIN_SET_WORDS : forall fx0 : YK11.FPState, tpin_set_words_spec (fx := fx0) B MT.
Hypothesis TPINS_CLEAR : forall fx0 : YK11.FPState, tpins_clear_spec (fx := fx0) B MT.
Hypothesis TREPLY : forall fx0 : YK11.FPState, treply_spec (fx := fx0) B MT.
Hypothesis TSUP_ADD : forall fx0 : YK11.FPState, tsup_add_spec (fx := fx0) B MT.
Hypothesis TSUP_AFTER_REPLY : forall fx0 : YK11.FPState, tsup_after_reply_spec (fx := fx0) B MT.
Hypothesis TSUP_BROADCAST : forall fx0 : YK11.FPState, tsup_broadcast_spec (fx := fx0) B MT.
Hypothesis TSUP_CALL : forall fx0 : YK11.FPState, tsup_call_spec (fx := fx0) B MT.
Hypothesis TSUP_CHAIN_CLEAR : forall fx0 : YK11.FPState, tsup_chain_clear_spec (fx := fx0) B MT.
Hypothesis TSUP_CONNECT : forall fx0 : YK11.FPState, tsup_connect_spec (fx := fx0) B MT.
Hypothesis TSUP_HOST_SETTING : forall fx0 : YK11.FPState, tsup_host_setting_spec (fx := fx0) B MT.
Hypothesis TSUP_INSTANCE_INFO : forall fx0 : YK11.FPState, tsup_instance_info_spec (fx := fx0) B MT.
Hypothesis TSUP_INSTANCE_VERB : forall fx0 : YK11.FPState, tsup_instance_verb_spec (fx := fx0) B MT.
Hypothesis TSUP_LV2_WORKER_SET : forall fx0 : YK11.FPState, tsup_lv2_worker_set_spec (fx := fx0) B MT.
Hypothesis TSUP_PIN_ACCEPT : forall fx0 : YK11.FPState, tsup_pin_accept_spec (fx := fx0) B MT.
Hypothesis TSUP_POLICY_SET : forall fx0 : YK11.FPState, tsup_policy_set_spec (fx := fx0) B MT.
Hypothesis TSUP_POOL_CONFIG : forall fx0 : YK11.FPState, tsup_pool_config_spec (fx := fx0) B MT.
Hypothesis TSUP_QUARANTINE_CLEAR : forall fx0 : YK11.FPState, tsup_quarantine_clear_spec (fx := fx0) B MT.
Hypothesis TSUP_REMOVE : forall fx0 : YK11.FPState, tsup_remove_spec (fx := fx0) B MT.
Hypothesis TSUP_REMOVE_ALL : forall fx0 : YK11.FPState, tsup_remove_all_spec (fx := fx0) B MT.
Hypothesis TSUP_REPLY_CODE : forall fx0 : YK11.FPState, tsup_reply_code_spec (fx := fx0) B MT.
Hypothesis TSUP_RESET : forall fx0 : YK11.FPState, tsup_reset_spec (fx := fx0) B MT.
Hypothesis TSUP_RESP : forall fx0 : YK11.FPState, tsup_resp_spec (fx := fx0) B MT.
Hypothesis TSUP_WORKER_ENV : forall fx0 : YK11.FPState, tsup_worker_env_spec (fx := fx0) B MT.
Hypothesis TSUP_WORKER_LIST : forall fx0 : YK11.FPState, tsup_worker_list_spec (fx := fx0) B MT.
Hypothesis TVERB_IS : forall fx0 : YK11.FPState, tverb_is_spec (fx := fx0) B MT.
(* the runtime entries (verbs_receive_c.v:262-279), at every FP state *)
Hypothesis SM4 : forall fx0 : YK11.FPState, astack_malloc_realizes (fx := fx0) SEGS B 4.
Hypothesis SH00 : forall fx0 : YK11.FPState, RtShadow.aset_shadow_realizes (fx := fx0) SEGS B (SIGMA CS___asan_set_shadow_00) 0.
Hypothesis SHF5 : forall fx0 : YK11.FPState, RtShadow.aset_shadow_realizes (fx := fx0) SEGS B (SIGMA CS___asan_set_shadow_f5) 0xf5.
Hypothesis SHF8 : forall fx0 : YK11.FPState, RtShadow.aset_shadow_realizes (fx := fx0) SEGS B (SIGMA CS___asan_set_shadow_f8) 0xf8.
Hypothesis STRLEN : forall fx0 : YK11.FPState, RtString.astrlen_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_strlen).
Hypothesis STRCMP : forall fx0 : YK11.FPState, RtString.astrcmp_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_strcmp).
Hypothesis STRNCMP : forall fx0 : YK11.FPState, RtString.astrncmp_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
Hypothesis STRCSPN : forall fx0 : YK11.FPState,
  RtString.astrcspn_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158.
Hypothesis STRTOK_R : forall fx0 : YK11.FPState, RtString.astrtok_r_realizes (fx := fx0) SEGS B (SIGMA CS_strtok_r) 0xa6bf8 0x604158.
Hypothesis AATOI : forall fx0 : YK11.FPState,
  RtNumber.aatoi_realizes (fx := fx0) SEGS B (SIGMA CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158.
Hypothesis ASTRDUP : forall fx0 : YK11.FPState,
  RtAlloc04.astrdup04_rule (fx := fx0) SEGS B MT (SIGMA CS___interceptor_trampoline_strdup) PC_STRDUP_RA0.
Hypothesis ASTRNDUP : forall fx0 : YK11.FPState,
  RtAlloc04.astrndup04_rule (fx := fx0) SEGS B MT (SIGMA CS___interceptor_trampoline_strndup) PC_STRNDUP_RA0.
Hypothesis AFREE : forall fx0 : YK11.FPState, afree04_rule (fx := fx0) SEGS B MT.
(* the allocator record and the laws of the meter (a Theorem Labs lane's RULING-STMT.md §1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTFL : YC5d.ameter_fs_laws MT.

Theorem tverbs_receive_closed : verbs_receive_c.tverbs_receive_spec B MT.
Proof.
exact (verbs_receive_top.tverbs_receive B MT PC_STRDUP_RA0 PC_STRNDUP_RA0
  TCHAIN_WORDS TDESCRIPTORS_ADD TDESCRIPTORS_GET TDESCRIPTORS_PANEL_GET TIS_INSTANCE_VERB TLV2_REFUSALS_FORGET TNUMBER
  TPIN_SET_WORDS TPINS_CLEAR TREPLY TSUP_ADD TSUP_AFTER_REPLY TSUP_BROADCAST TSUP_CALL TSUP_CHAIN_CLEAR TSUP_CONNECT
  TSUP_HOST_SETTING TSUP_INSTANCE_INFO TSUP_INSTANCE_VERB TSUP_LV2_WORKER_SET TSUP_PIN_ACCEPT TSUP_POLICY_SET
  TSUP_POOL_CONFIG TSUP_QUARANTINE_CLEAR TSUP_REMOVE TSUP_REMOVE_ALL TSUP_REPLY_CODE TSUP_RESET TSUP_RESP
  TSUP_WORKER_ENV TSUP_WORKER_LIST TVERB_IS
  SM4 (CmdRecRest.cmd_stack_malloc_progress B) (CmdRecRest.cmd_astack_free_law B) (CmdRecRest.cmd_frame_flag_law B)
  SH00 SHF5 SHF8 STRLEN STRCMP STRNCMP STRCSPN STRTOK_R AATOI ASTRDUP ASTRNDUP AFREE
  HB (CmdRecImg.cmd_img_facts_tfib B HB) (CmdRecRest.cmd_palib B HB) (CmdRecRest.cmd_palibf B HB)
  (CmdRecRest.cmd_model_laws B HB) MTL MTFL
  CmdRecRest.cmd_val_objs_PB CmdRecRest.cmd_val_his_PB CmdRecRest.cmd_sig_prog_PB (CmdRecRest.cmd_prw_tfib B HB)).
Qed.
End closed.
