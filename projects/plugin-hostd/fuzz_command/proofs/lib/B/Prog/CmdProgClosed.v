(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the twin of lib/A/Prog/CmdProgClosed.v for the ASan+UBSan build
   fuzz_command.asan-ubsan: module paths A -> B, core files AE2k / AD2l / AF0q -> YE2k / YD2l / YF0q, and the
   runtime closers of this build. *)
(* The program side of plugin-hostd/fuzz_command's ASan+UBSan proof, composed at the pinned image B: every one of the
   64 program functions' contracts (`t<fn>_spec`, lib/B/Prog/<fn>_c.v) at CmdImg.v's instance PB_cmd (segments
   tfibsegs, lib/B/YB1v.v), the sink head YE2k.tfib_sink_head, the allocator record YD2l.CmdB (YD2l.CmdB_syms) and
   the trivial meter YCbp.ameter_triv (ameter_triv_laws, ameter_triv_fs_laws), at every FP state, from
   - each function's closed theorem `t<fn>_closed` (lib/B/Prog/<Fn>Closed.v and the group files CmdA9ClosedB.v and
     CmdReplyWalksClosed.v), which takes only the record CmdBSyms, the meter's laws and the contracts of its callees;
   - the runtime entries' closers: lib/B/Rt/RtClosed.v (the shadow fills, the side-stack entries, the string, number
     and printf interceptors), lib/B/Rt/Strnlen.v, lib/B/YE2s.v (bcmp), lib/B/Rt/RtLAsanMemcpy.v and
     RtLAsanMemset.v (the intrinsics), the malloc chain lib/B/YF0w.v (malloc and asan_malloc), the strdup / strndup
     / malloc body walks of lib/B/Rt (RtDStrdupX.v, RtDStrndup.v, RtDMallocBody.v), and the allocator rules of the
     core (YCbp.v's amalloc04_rule_triv, afree04_rule_triv, afree_null04_rule_triv; YF0q.v's afree_realizes_closed).
   Nothing is assumed beyond them: the file has no Section hypothesis.
   cmd_ltoi_all_B is lib/B/Prog/CmdLibX.v's premise HLTOI, and cmd_lib_x_final_B is CmdLibX's cmd_lib_x_closed
   with it. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d YG0q YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require ZTraceSpec AgreeShape.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m YB1v YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2k YD2l YF0q YF0w YE2s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Rt Require StrnlenDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtDefs RtAPI RtString RtNumber RtFormat RtStack
  RtShadow RtAlloc04 RtDDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtClosed Strnlen RtLAsanMemcpy RtLAsanMemset
  RtDStrdupX RtDStrndup RtDMallocBody RtD04d RtD04n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj
  CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecRest CmdLibX.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require
LLVMFuzzerTestOneInput_c answer_c answer_code_c arg_line_c arg_s_c chain_words_c check_arity_c check_refusal_c
check_reply_answer_c check_reply_c check_round_trip_c check_words_add_c check_words_c check_words_chain_c
check_words_pin_set_c descriptors_add_c descriptors_get_c descriptors_panel_get_c hand_back_c is_instance_verb_c
joined_c lv2_refusals_forget_c mix_call_c number_c pin_set_words_c pins_clear_c pins_set_c rec_calls_copy_c
rec_calls_equal_c rec_calls_free_c rec_canonical_c rec_clear_c rec_code_declared_c rec_shape_of_c record_c reply_c
send_message_c socket_send_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c sup_chain_c sup_chain_clear_c
sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c sup_pin_accept_c
sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_all_c sup_remove_c sup_reply_code_c sup_reset_c
sup_resp_c sup_worker_env_c sup_worker_list_c syntax_reply_matches_c verb_is_c verbs_receive_c xmalloc_c.
(* the functions' closed theorems *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require
AnswerClosed AnswerCodeClosed ArgLineClosed ArgSClosed ChainWordsClosed CheckArityClosed CheckRefusalClosed
CheckWordsAddClosed CheckWordsChainClosed CheckWordsClosed CheckWordsPinSetClosed CmdA9ClosedB CmdReplyWalksClosed
DescriptorsAddClosed DescriptorsGetClosed DescriptorsPanelGetClosed HandBackClosed IsInstanceVerbClosed
LLVMFuzzerTestOneInputClosed Lv2RefusalsForgetClosed MixCallClosed NumberClosed PinSetWordsClosed PinsClearClosed
PinsSetClosed RecClearClosed RecordClosed ReplyClosed SocketSendClosed SupAddClosed SupAfterReplyClosed SupCallClosed
SupChainClearClosed SupChainClosed SupConnectClosed SupHostSettingClosed SupInstanceInfoClosed SupInstanceVerbClosed
SupLv2WorkerSetClosed SupPinAcceptClosed SupPolicySetClosed SupPoolConfigClosed SupQuarantineClearClosed
SupRemoveAllClosed SupResetClosed SupRespClosed SupWorkerEnvClosed SupWorkerListClosed VerbIsClosed VerbsReceiveClosed
sup_broadcast_closed sup_remove_closed.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SK0 := YE2k.tfib_sink_head.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PB_cmd c).
#[local] Notation B := YD2l.CmdB.
#[local] Notation MT := YCbp.ameter_triv.
#[local] Notation HB := YD2l.CmdB_syms.
#[local] Notation MTL := YCbp.ameter_triv_laws.
#[local] Notation MTFL := YCbp.ameter_triv_fs_laws.
#[local] Notation LAWS := (YG0q.AR_laws_ok SEGS B).
#[local] Notation TL := (CmdRecRest.cmd_palib B HB).
#[local] Notation ML := (CmdRecRest.cmd_model_laws B HB).
#[local] Notation ENV := (@CmdPaLib.pal_env rc cmd_listing PB_cmd B TL).

(** * The runtime entries' contracts at the program's form, from their closers *)
(* __asan::asan_malloc (0x34574) with a trace its caller built, from the malloc chain (YF0w.v cmd_amalloc_inner) *)
Lemma r_inner : forall fx0 : YK11.FPState,
  @RtDDefs.amalloc_inner_realizes fx0 rc tfibsegs B RtDDefs.PC_asan_malloc.
Proof. exact (fun fx0 => @YF0w.cmd_amalloc_inner fx0 rc B HB (fun t => eq_refl)). Qed.
(* the malloc interceptor's body (0x58ba4), entered with the unwinder pc 0x58c6c, from its walk *)
Lemma r_malloc_body : forall fx0 : YK11.FPState,
  @RtDDefs.amalloc_body_realizes fx0 rc tfibsegs B RtDDefs.PC_malloc_body RtAPI.PC_STRNDUP_RA0.
Proof. exact (fun fx0 => @RtDMallocBody.cmd_amalloc_body fx0 rc B HB LAWS (r_inner fx0)). Qed.
(* malloc (YF0w.v tfib_amalloc_realizes) and free, and the allocator rules of the trivial meter (YCbp.v) over them *)
Lemma r_amalloc : forall fx0 : YK11.FPState, @amalloc_realizes fx0 rc tfibsegs B.
Proof. exact (fun fx0 => @YF0w.tfib_amalloc_realizes fx0 rc B HB (fun t => eq_refl)). Qed.
Lemma r_malloc4 : forall fx0 : YK11.FPState, @YC5d.amalloc04_rule fx0 rc SK0 SEGS B MT.
Proof.
exact (fun fx0 => @YCbp.amalloc04_rule_triv fx0 rc SK0 SEGS B CmdImg.cmd_segs_low ENV LAWS ML (r_amalloc fx0)).
Qed.
Lemma r_free4 : forall fx0 : YK11.FPState, @YC5d.afree04_rule fx0 rc SK0 SEGS B MT.
Proof.
exact (fun fx0 => @YCbp.afree04_rule_triv fx0 rc SK0 SEGS B CmdImg.cmd_segs_low ENV LAWS ML
  (@YF0q.afree_realizes_closed fx0 rc B HB (fun t => eq_refl))).
Qed.
Lemma r_free_null4 : forall fx0 : YK11.FPState, @YC5d.afree_null04_rule fx0 rc SK0 SEGS B MT.
Proof.
exact (fun fx0 => @YCbp.afree_null04_rule_triv fx0 rc SK0 SEGS B CmdImg.cmd_segs_low ENV LAWS ML
  (@YF0q.afree_realizes_closed fx0 rc B HB (fun t => eq_refl))).
Qed.
(* strdup (0x45228) and strndup (0x45184): the 04 rules of the trivial meter (RtD04d.v, RtD04n.v) over the entries'
   walks *)
Lemma r_strdup4 : forall fx0 : YK11.FPState,
  @RtAlloc04.astrdup04_rule fx0 rc SK0 SEGS B MT (SIG CS___interceptor_trampoline_strdup) RtAPI.PC_STRDUP_RA0.
Proof.
exact (fun fx0 => @RtD04d.astrdup04_rule_triv fx0 rc SK0 SEGS B CmdImg.cmd_segs_low ENV LAWS ML
  (SIG CS___interceptor_trampoline_strdup) RtAPI.PC_STRDUP_RA0
  (@RtDStrdupX.cmd_strdup fx0 rc B LAWS HB (r_inner fx0))).
Qed.
Lemma r_strndup4 : forall fx0 : YK11.FPState,
  @RtAlloc04.astrndup04_rule fx0 rc SK0 SEGS B MT (SIG CS___interceptor_trampoline_strndup) RtAPI.PC_STRNDUP_RA0.
Proof.
exact (fun fx0 => @RtD04n.astrndup04_rule_triv fx0 rc SK0 SEGS B CmdImg.cmd_segs_low ENV LAWS ML
  (SIG CS___interceptor_trampoline_strndup) RtAPI.PC_STRNDUP_RA0 RtAPI.PC_STRNDUP_MID
  (@RtDStrndup.cmd_strndup fx0 rc B LAWS HB (r_malloc_body fx0))).
Qed.
(* the intrinsics __asan_memcpy and __asan_memset (RtLAsanMemcpy.v, RtLAsanMemset.v over YE2q.v, YE2r.v) *)
Lemma r_memcpy : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Proof. exact (fun fx0 => @RtLAsanMemcpy.cmd_asan_memcpy fx0 rc B LAWS HB). Qed.
Lemma r_memset : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG CS___asan_memset).
Proof. exact (fun fx0 => @RtLAsanMemset.cmd_asan_memset fx0 rc B LAWS HB). Qed.
(* the bcmp interceptor (0x451a0, YE2s.v) *)
Lemma r_bcmp : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_bcmp).
Proof. exact (fun fx0 => @YE2s.bcmp_icpt_contract fx0 rc B LAWS HB). Qed.
(* the string and number interceptors (RtClosed.v; strnlen by Strnlen.v) *)
Lemma r_strlen : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Proof. exact (fun fx0 => @RtClosed.cmd_strlen_closed fx0 rc B HB). Qed.
Lemma r_strcmp : forall fx0 : YK11.FPState,
  @RtString.astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
Proof. exact (fun fx0 => @RtClosed.cmd_strcmp_closed fx0 rc B HB). Qed.
Lemma r_strncmp : forall fx0 : YK11.FPState,
  @RtString.astrncmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strncmp).
Proof. exact (fun fx0 => @RtClosed.cmd_strncmp_closed fx0 rc B HB). Qed.
Lemma r_strspn : forall fx0 : YK11.FPState,
  @RtString.astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa6bf8 0x604158.
Proof. exact (fun fx0 => @RtClosed.cmd_strspn_closed fx0 rc B HB). Qed.
Lemma r_strcspn : forall fx0 : YK11.FPState,
  @RtString.astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158.
Proof. exact (fun fx0 => @RtClosed.cmd_strcspn_closed fx0 rc B HB). Qed.
Lemma r_strtok_r : forall fx0 : YK11.FPState,
  @RtString.astrtok_r_realizes fx0 rc SEGS B (SIG CS_strtok_r) 0xa6bf8 0x604158.
Proof. exact (fun fx0 => @RtClosed.cmd_strtok_r_closed fx0 rc B HB). Qed.
Lemma r_strnlen : forall fx0 : YK11.FPState,
  @StrnlenDef.astrnlen_whole_realizesM fx0 rc SEGS B 0x10358 0x10378 (SIG CS___interceptor_trampoline_strnlen).
Proof. exact (fun fx0 => @Strnlen.strnlen_icpt_realizesM fx0 rc B LAWS HB). Qed.
Lemma r_memchr : forall fx0 : YK11.FPState,
  @RtString.amemchr0_nf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_memchr).
Proof. exact (fun fx0 => @RtClosed.cmd_memchr_nf_closed fx0 rc B HB). Qed.
Lemma r_strcat : forall fx0 : YK11.FPState,
  @RtString.astrcat_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcat).
Proof. exact (fun fx0 => @RtClosed.cmd_strcat_closed fx0 rc B HB). Qed.
Lemma r_atoi : forall fx0 : YK11.FPState,
  @RtNumber.aatoi_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158.
Proof. exact (fun fx0 => @RtClosed.cmd_atoi_closed fx0 rc B HB). Qed.
Lemma r_strtol : forall fx0 : YK11.FPState,
  @RtNumber.astrtol_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strtol) 0xa6bf8 0x604158.
Proof. exact (fun fx0 => @RtClosed.cmd_strtol_closed fx0 rc B HB). Qed.
(* snprintf (0x451d0) and sprintf (0x451cc) on the printf route (RtClosed.v over RtFSnprintf.v, RtFSprintf.v) *)
Lemma r_snprintf : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Proof. exact (fun fx0 => @RtClosed.cmd_snprintf_closed fx0 rc B HB). Qed.
Lemma r_sprintf : forall fx0 : YK11.FPState,
  @RtFormat.asprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_sprintf) 0xa6bf8 0x604158.
Proof. exact (fun fx0 => @RtClosed.cmd_sprintf_closed fx0 rc B HB). Qed.
(* the side-stack entries and the shadow fills (RtClosed.v) *)
Lemma r_sm0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Proof. exact (fun fx0 => @RtClosed.cmd_stack_malloc0_contract_closed fx0 rc B HB). Qed.
Lemma r_sm1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Proof. exact (fun fx0 => @RtClosed.cmd_stack_malloc1_contract_closed fx0 rc B HB). Qed.
Lemma r_sm3 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 3.
Proof. exact (fun fx0 => @RtClosed.cmd_stack_malloc3_contract_closed fx0 rc B HB). Qed.
Lemma r_sm4 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 4.
Proof. exact (fun fx0 => @RtClosed.cmd_stack_malloc4_contract_closed fx0 rc B HB). Qed.
Lemma r_sm5 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 5.
Proof. exact (fun fx0 => @RtClosed.cmd_stack_malloc5_contract_closed fx0 rc B HB). Qed.
Lemma r_sm7 : forall fx0 : YK11.FPState,
  @RtStack.astack_malloc_sz_realizes fx0 rc SEGS B (SIG CS___asan_stack_malloc_7) 7.
Proof. exact (fun fx0 => @RtClosed.cmd_stack_malloc7_contract_closed fx0 rc B HB). Qed.
Lemma r_sf5 : forall fx0 : YK11.FPState,
  @RtStack.astack_free_cls_realizes fx0 rc SEGS B (SIG CS___asan_stack_free_5) 5.
Proof. exact (fun fx0 => @RtClosed.cmd_stack_free5_contract_closed fx0 rc B HB). Qed.
Lemma r_sf7 : forall fx0 : YK11.FPState,
  @RtStack.astack_free_realizes fx0 rc SEGS B (SIG CS___asan_stack_free_7) 7.
Proof. exact (fun fx0 => @RtClosed.cmd_stack_free7_contract_closed fx0 rc B HB). Qed.
Lemma r_sh00 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_00) 0.
Proof. exact (fun fx0 => @RtClosed.cmd_set_shadow_00_closed fx0 rc B HB). Qed.
Lemma r_shf5 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f5) 0xf5.
Proof. exact (fun fx0 => @RtClosed.cmd_set_shadow_f5_closed fx0 rc B HB). Qed.
Lemma r_shf8 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f8) 0xf8.
Proof. exact (fun fx0 => @RtClosed.cmd_set_shadow_f8_closed fx0 rc B HB). Qed.

(** * The program functions, callees first; each by its closed theorem *)
(* mix_call: tmix_call_closed (MixCallClosed.v:30) *)
Lemma cl_mix_call : forall fx0 : YK11.FPState, @B.Prog.mix_call_c.tmix_call_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @MixCallClosed.tmix_call_closed fx0 rc B MT HB r_strlen). Qed.
(* xmalloc: txmalloc_closed (CmdA9ClosedB.v:49) *)
Lemma cl_xmalloc : forall fx0 : YK11.FPState, @B.Prog.xmalloc_c.txmalloc_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @CmdA9ClosedB.txmalloc_closed fx0 rc B MT HB r_malloc4). Qed.
(* rec_calls_free: trec_calls_free_closed (CmdA9ClosedB.v:56) *)
Lemma cl_rec_calls_free : forall fx0 : YK11.FPState,
  @B.Prog.rec_calls_free_c.trec_calls_free_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @CmdA9ClosedB.trec_calls_free_closed fx0 rc B MT HB MTL r_free4). Qed.
(* rec_calls_equal: trec_calls_equal_closed (CmdA9ClosedB.v:64) *)
Lemma cl_rec_calls_equal : forall fx0 : YK11.FPState,
  @B.Prog.rec_calls_equal_c.trec_calls_equal_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @CmdA9ClosedB.trec_calls_equal_closed fx0 rc B MT HB r_strcmp). Qed.
(* rec_canonical: trec_canonical_closed (CmdA9ClosedB.v:71) *)
Lemma cl_rec_canonical : forall fx0 : YK11.FPState,
  @B.Prog.rec_canonical_c.trec_canonical_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @CmdA9ClosedB.trec_canonical_closed fx0 rc B MT HB cl_xmalloc). Qed.
(* joined: tjoined_closed (CmdA9ClosedB.v:78) *)
Lemma cl_joined : forall fx0 : YK11.FPState, @B.Prog.joined_c.tjoined_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @CmdA9ClosedB.tjoined_closed fx0 rc B MT HB r_malloc4 r_memcpy r_strlen). Qed.
(* rec_calls_copy: trec_calls_copy_closed (CmdA9ClosedB.v:88) *)
Lemma cl_rec_calls_copy : forall fx0 : YK11.FPState,
  @B.Prog.rec_calls_copy_c.trec_calls_copy_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @CmdA9ClosedB.trec_calls_copy_closed fx0 rc B MT HB MTL cl_xmalloc r_memcpy r_strlen).
Qed.
(* record: trecord_closed (RecordClosed.v:39) *)
Lemma cl_record : forall fx0 : YK11.FPState, @B.Prog.record_c.trecord_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @RecordClosed.trecord_closed fx0 rc B MT HB MTL cl_rec_calls_free). Qed.
(* arg_s: targ_s_closed (ArgSClosed.v:41) *)
Lemma cl_arg_s : forall fx0 : YK11.FPState, @B.Prog.arg_s_c.targ_s_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @ArgSClosed.targ_s_closed fx0 rc B MT HB MTL cl_xmalloc r_memcpy r_strlen). Qed.
(* hand_back: thand_back_closed (HandBackClosed.v:43) *)
Lemma cl_hand_back : forall fx0 : YK11.FPState, @B.Prog.hand_back_c.thand_back_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @HandBackClosed.thand_back_closed fx0 rc B MT HB MTL cl_xmalloc r_free4 r_free_null4 r_memcpy
  r_strlen).
Qed.
(* answer: tanswer_closed (AnswerClosed.v:46) *)
Lemma cl_answer : forall fx0 : YK11.FPState, @B.Prog.answer_c.tanswer_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @AnswerClosed.tanswer_closed fx0 rc B MT HB MTL MTFL cl_hand_back cl_mix_call r_sm7 r_sf7 r_sh00
  r_shf8 r_snprintf).
Qed.
(* answer_code: tanswer_code_closed (AnswerCodeClosed.v:40) *)
Lemma cl_answer_code : forall fx0 : YK11.FPState,
  @B.Prog.answer_code_c.tanswer_code_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @AnswerCodeClosed.tanswer_code_closed fx0 rc B MT HB MTL MTFL cl_hand_back r_free4 r_sm1
  r_snprintf).
Qed.
(* arg_line: targ_line_closed (ArgLineClosed.v:40) *)
Lemma cl_arg_line : forall fx0 : YK11.FPState, @B.Prog.arg_line_c.targ_line_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @ArgLineClosed.targ_line_closed fx0 rc B MT HB MTL cl_rec_canonical r_strlen). Qed.
(* socket_send: tsocket_send_closed (SocketSendClosed.v:37) *)
Lemma cl_socket_send : forall fx0 : YK11.FPState,
  @B.Prog.socket_send_c.tsocket_send_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SocketSendClosed.tsocket_send_closed fx0 rc B MT HB MTL cl_xmalloc r_free4 r_free_null4 r_memset
  r_memcpy).
Qed.
(* reply: treply_closed (ReplyClosed.v:36) *)
Lemma cl_reply : forall fx0 : YK11.FPState, @B.Prog.reply_c.treply_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @ReplyClosed.treply_closed fx0 rc B MT HB MTL cl_socket_send r_strlen r_free4). Qed.
(* rec_clear: trec_clear_closed (RecClearClosed.v:37) *)
Lemma cl_rec_clear : forall fx0 : YK11.FPState, @B.Prog.rec_clear_c.trec_clear_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @RecClearClosed.trec_clear_closed fx0 rc B MT HB MTL cl_rec_calls_free r_free4 r_free_null4
  r_memset).
Qed.
(* rec_code_declared: trec_code_declared_closed (CmdReplyWalksClosed.v:41) *)
Lemma cl_rec_code_declared : forall fx0 : YK11.FPState,
  @B.Prog.rec_code_declared_c.trec_code_declared_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @CmdReplyWalksClosed.trec_code_declared_closed fx0 rc B MT HB). Qed.
(* sup_reply_code: tsup_reply_code_closed (CmdReplyWalksClosed.v:47) *)
Lemma cl_sup_reply_code : forall fx0 : YK11.FPState,
  @B.Prog.sup_reply_code_c.tsup_reply_code_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @CmdReplyWalksClosed.tsup_reply_code_closed fx0 rc B MT HB r_strncmp r_atoi). Qed.
(* syntax_reply_matches: tsyntax_reply_matches_closed (CmdReplyWalksClosed.v:57) *)
Lemma cl_syntax_reply_matches : forall fx0 : YK11.FPState,
  @B.Prog.syntax_reply_matches_c.tsyntax_reply_matches_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @CmdReplyWalksClosed.tsyntax_reply_matches_closed fx0 rc B MT HB r_strcspn r_bcmp).
Qed.
(* check_reply_answer: tcheck_reply_answer_closed (CmdReplyWalksClosed.v:67) *)
Lemma cl_check_reply_answer : forall fx0 : YK11.FPState,
  @B.Prog.check_reply_answer_c.tcheck_reply_answer_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @CmdReplyWalksClosed.tcheck_reply_answer_closed fx0 rc B MT HB cl_sup_reply_code r_strcmp
  r_strcspn r_strncmp).
Qed.
(* rec_shape_of: trec_shape_of_closed (CmdReplyWalksClosed.v:80) *)
Lemma cl_rec_shape_of : forall fx0 : YK11.FPState,
  @B.Prog.rec_shape_of_c.trec_shape_of_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @CmdReplyWalksClosed.trec_shape_of_closed fx0 rc B MT HB r_strlen r_bcmp). Qed.
(* check_reply: tcheck_reply_closed (CmdReplyWalksClosed.v:105) *)
Lemma cl_check_reply : forall fx0 : YK11.FPState,
  @B.Prog.check_reply_c.tcheck_reply_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @CmdReplyWalksClosed.tcheck_reply_closed fx0 rc B MT HB cl_check_reply_answer
  cl_sup_reply_code cl_rec_code_declared cl_rec_shape_of cl_syntax_reply_matches r_sm1 r_memchr r_strlen r_snprintf
  r_strcmp).
Qed.
(* is_instance_verb: tis_instance_verb_closed (IsInstanceVerbClosed.v:36) *)
Lemma cl_is_instance_verb : forall fx0 : YK11.FPState,
  @B.Prog.is_instance_verb_c.tis_instance_verb_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @IsInstanceVerbClosed.tis_instance_verb_closed fx0 rc B MT HB r_strcspn r_strncmp). Qed.
(* verb_is: tverb_is_closed (VerbIsClosed.v:34) *)
Lemma cl_verb_is : forall fx0 : YK11.FPState, @B.Prog.verb_is_c.tverb_is_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @VerbIsClosed.tverb_is_closed fx0 rc B MT HB r_strcspn r_strncmp). Qed.
(* number: tnumber_closed (NumberClosed.v:38) *)
Lemma cl_number : forall fx0 : YK11.FPState, @B.Prog.number_c.tnumber_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @NumberClosed.tnumber_closed fx0 rc B MT HB r_sm0 r_strtol). Qed.
(* sup_resp: tsup_resp_closed (SupRespClosed.v:40) *)
Lemma cl_sup_resp : forall fx0 : YK11.FPState, @B.Prog.sup_resp_c.tsup_resp_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupRespClosed.tsup_resp_closed fx0 rc B MT HB MTFL cl_xmalloc r_sm1 r_snprintf r_strlen r_memcpy).
Qed.
(* sup_chain: tsup_chain_closed (SupChainClosed.v:41) *)
Lemma cl_sup_chain : forall fx0 : YK11.FPState, @B.Prog.sup_chain_c.tsup_chain_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupChainClosed.tsup_chain_closed fx0 rc B MT HB MTL MTFL cl_record cl_xmalloc cl_arg_s
  cl_rec_shape_of cl_answer r_sm1 r_snprintf r_sprintf r_free4).
Qed.
(* chain_words: tchain_words_closed (ChainWordsClosed.v:41) *)
Lemma cl_chain_words : forall fx0 : YK11.FPState,
  @B.Prog.chain_words_c.tchain_words_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @ChainWordsClosed.tchain_words_closed fx0 rc B MT HB MTL MTFL cl_number cl_sup_chain cl_sup_resp
  r_sm3 r_shf5).
Qed.
(* descriptors_add: tdescriptors_add_closed (DescriptorsAddClosed.v:39) *)
Lemma cl_descriptors_add : forall fx0 : YK11.FPState,
  @B.Prog.descriptors_add_c.tdescriptors_add_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @DescriptorsAddClosed.tdescriptors_add_closed fx0 rc B MT HB MTL cl_record cl_arg_s cl_mix_call).
Qed.
(* descriptors_get: tdescriptors_get_closed (DescriptorsGetClosed.v:34) *)
Lemma cl_descriptors_get : forall fx0 : YK11.FPState,
  @B.Prog.descriptors_get_c.tdescriptors_get_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @DescriptorsGetClosed.tdescriptors_get_closed fx0 rc B MT HB MTL cl_record cl_arg_s cl_rec_shape_of
  cl_answer).
Qed.
(* descriptors_panel_get: tdescriptors_panel_get_closed (DescriptorsPanelGetClosed.v:36) *)
Lemma cl_descriptors_panel_get : forall fx0 : YK11.FPState,
  @B.Prog.descriptors_panel_get_c.tdescriptors_panel_get_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @DescriptorsPanelGetClosed.tdescriptors_panel_get_closed fx0 rc B MT HB MTL cl_record cl_arg_s
  cl_rec_shape_of cl_answer).
Qed.
(* lv2_refusals_forget: tlv2_refusals_forget_closed (Lv2RefusalsForgetClosed.v:39) *)
Lemma cl_lv2_refusals_forget : forall fx0 : YK11.FPState,
  @B.Prog.lv2_refusals_forget_c.tlv2_refusals_forget_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @Lv2RefusalsForgetClosed.tlv2_refusals_forget_closed fx0 rc B MT HB MTL cl_record cl_arg_s
  cl_mix_call).
Qed.
(* pins_set: tpins_set_closed (PinsSetClosed.v:40) *)
Lemma cl_pins_set : forall fx0 : YK11.FPState, @B.Prog.pins_set_c.tpins_set_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @PinsSetClosed.tpins_set_closed fx0 rc B MT HB MTL cl_record cl_arg_s cl_mix_call cl_answer_code).
Qed.
(* pins_clear: tpins_clear_closed (PinsClearClosed.v:41) *)
Lemma cl_pins_clear : forall fx0 : YK11.FPState, @B.Prog.pins_clear_c.tpins_clear_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @PinsClearClosed.tpins_clear_closed fx0 rc B MT HB MTL cl_record cl_arg_s cl_mix_call
  cl_answer_code).
Qed.
(* pin_set_words: tpin_set_words_closed (PinSetWordsClosed.v:39) *)
Lemma cl_pin_set_words : forall fx0 : YK11.FPState,
  @B.Prog.pin_set_words_c.tpin_set_words_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @PinSetWordsClosed.tpin_set_words_closed fx0 rc B MT HB MTL cl_pins_set cl_lv2_refusals_forget
  r_strlen r_strncmp).
Qed.
(* sup_add: tsup_add_closed (SupAddClosed.v:42) *)
Lemma cl_sup_add : forall fx0 : YK11.FPState, @B.Prog.sup_add_c.tsup_add_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupAddClosed.tsup_add_closed fx0 rc B MT HB MTL MTFL cl_record cl_arg_s cl_mix_call cl_hand_back
  cl_answer r_sm1 r_snprintf).
Qed.
(* sup_after_reply: tsup_after_reply_closed (SupAfterReplyClosed.v:39) *)
Lemma cl_sup_after_reply : forall fx0 : YK11.FPState,
  @B.Prog.sup_after_reply_c.tsup_after_reply_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupAfterReplyClosed.tsup_after_reply_closed fx0 rc B MT HB MTL MTFL cl_record cl_arg_s r_sm0
  r_snprintf).
Qed.
(* sup_call: tsup_call_closed (SupCallClosed.v:42) *)
Lemma cl_sup_call : forall fx0 : YK11.FPState, @B.Prog.sup_call_c.tsup_call_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupCallClosed.tsup_call_closed fx0 rc B MT HB MTL MTFL cl_record cl_arg_s cl_arg_line cl_answer
  r_sm0 r_snprintf).
Qed.
(* sup_chain_clear: tsup_chain_clear_closed (SupChainClearClosed.v:43) *)
Lemma cl_sup_chain_clear : forall fx0 : YK11.FPState,
  @B.Prog.sup_chain_clear_c.tsup_chain_clear_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupChainClearClosed.tsup_chain_clear_closed fx0 rc B MT HB MTL MTFL cl_record cl_arg_s
  cl_rec_shape_of cl_answer r_sm0 r_snprintf).
Qed.
(* sup_connect: tsup_connect_closed (SupConnectClosed.v:36) *)
Lemma cl_sup_connect : forall fx0 : YK11.FPState, @B.Prog.sup_connect_c.tsup_connect_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupConnectClosed.tsup_connect_closed fx0 rc B MT HB MTL cl_record cl_arg_s cl_arg_line cl_answer).
Qed.
(* sup_host_setting: tsup_host_setting_closed (SupHostSettingClosed.v:43) *)
Lemma cl_sup_host_setting : forall fx0 : YK11.FPState,
  @B.Prog.sup_host_setting_c.tsup_host_setting_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupHostSettingClosed.tsup_host_setting_closed fx0 rc B MT HB MTL MTFL cl_record cl_arg_line
  cl_arg_s cl_xmalloc cl_mix_call r_sm0 r_snprintf r_free4 r_strlen r_strcat).
Qed.
(* sup_instance_info: tsup_instance_info_closed (SupInstanceInfoClosed.v:40) *)
Lemma cl_sup_instance_info : forall fx0 : YK11.FPState,
  @B.Prog.sup_instance_info_c.tsup_instance_info_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupInstanceInfoClosed.tsup_instance_info_closed fx0 rc B MT HB MTL MTFL cl_record cl_arg_s
  cl_rec_shape_of cl_answer r_sm0 r_snprintf).
Qed.
(* sup_instance_verb: tsup_instance_verb_closed (SupInstanceVerbClosed.v:43) *)
Lemma cl_sup_instance_verb : forall fx0 : YK11.FPState,
  @B.Prog.sup_instance_verb_c.tsup_instance_verb_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupInstanceVerbClosed.tsup_instance_verb_closed fx0 rc B MT HB MTL MTFL cl_record cl_arg_line
  cl_arg_s cl_rec_shape_of cl_answer r_sm0 r_snprintf r_strspn r_strcspn).
Qed.
(* sup_lv2_worker_set: tsup_lv2_worker_set_closed (SupLv2WorkerSetClosed.v:38) *)
Lemma cl_sup_lv2_worker_set : forall fx0 : YK11.FPState,
  @B.Prog.sup_lv2_worker_set_c.tsup_lv2_worker_set_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupLv2WorkerSetClosed.tsup_lv2_worker_set_closed fx0 rc B MT HB MTL cl_record cl_arg_s
  cl_rec_shape_of cl_answer).
Qed.
(* sup_pin_accept: tsup_pin_accept_closed (SupPinAcceptClosed.v:39) *)
Lemma cl_sup_pin_accept : forall fx0 : YK11.FPState,
  @B.Prog.sup_pin_accept_c.tsup_pin_accept_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupPinAcceptClosed.tsup_pin_accept_closed fx0 rc B MT HB MTL cl_record cl_arg_s cl_rec_shape_of
  cl_answer).
Qed.
(* sup_policy_set: tsup_policy_set_closed (SupPolicySetClosed.v:35) *)
Lemma cl_sup_policy_set : forall fx0 : YK11.FPState,
  @B.Prog.sup_policy_set_c.tsup_policy_set_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupPolicySetClosed.tsup_policy_set_closed fx0 rc B MT HB MTL cl_record cl_arg_s cl_rec_shape_of
  cl_answer).
Qed.
(* sup_pool_config: tsup_pool_config_closed (SupPoolConfigClosed.v:43) *)
Lemma cl_sup_pool_config : forall fx0 : YK11.FPState,
  @B.Prog.sup_pool_config_c.tsup_pool_config_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupPoolConfigClosed.tsup_pool_config_closed fx0 rc B MT HB MTL MTFL cl_record cl_arg_s
  cl_rec_shape_of cl_answer r_sm0 r_snprintf).
Qed.
(* sup_quarantine_clear: tsup_quarantine_clear_closed (SupQuarantineClearClosed.v:40) *)
Lemma cl_sup_quarantine_clear : forall fx0 : YK11.FPState,
  @B.Prog.sup_quarantine_clear_c.tsup_quarantine_clear_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupQuarantineClearClosed.tsup_quarantine_clear_closed fx0 rc B MT HB MTL cl_record cl_arg_s
  cl_rec_shape_of cl_answer).
Qed.
(* sup_remove_all: tsup_remove_all_closed (SupRemoveAllClosed.v:37) *)
Lemma cl_sup_remove_all : forall fx0 : YK11.FPState,
  @B.Prog.sup_remove_all_c.tsup_remove_all_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @SupRemoveAllClosed.tsup_remove_all_closed fx0 rc B MT HB MTL cl_record cl_answer). Qed.
(* sup_remove: tsup_remove_closed (sup_remove_closed.v:41) *)
Lemma cl_sup_remove : forall fx0 : YK11.FPState, @B.Prog.sup_remove_c.tsup_remove_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @sup_remove_closed.tsup_remove_closed fx0 rc B MT HB MTL MTFL cl_record cl_arg_s cl_answer r_sm0
  r_snprintf).
Qed.
(* sup_reset: tsup_reset_closed (SupResetClosed.v:39) *)
Lemma cl_sup_reset : forall fx0 : YK11.FPState, @B.Prog.sup_reset_c.tsup_reset_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupResetClosed.tsup_reset_closed fx0 rc B MT HB MTL cl_record cl_arg_s cl_rec_shape_of cl_answer).
Qed.
(* sup_worker_env: tsup_worker_env_closed (SupWorkerEnvClosed.v:42) *)
Lemma cl_sup_worker_env : forall fx0 : YK11.FPState,
  @B.Prog.sup_worker_env_c.tsup_worker_env_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupWorkerEnvClosed.tsup_worker_env_closed fx0 rc B MT HB MTL cl_record cl_arg_s cl_rec_shape_of
  cl_answer).
Qed.
(* sup_worker_list: tsup_worker_list_closed (SupWorkerListClosed.v:39) *)
Lemma cl_sup_worker_list : forall fx0 : YK11.FPState,
  @B.Prog.sup_worker_list_c.tsup_worker_list_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @SupWorkerListClosed.tsup_worker_list_closed fx0 rc B MT HB MTL cl_record cl_rec_shape_of
  cl_answer).
Qed.
(* sup_broadcast: tsup_broadcast_closed (sup_broadcast_closed.v:40) *)
Lemma cl_sup_broadcast : forall fx0 : YK11.FPState,
  @B.Prog.sup_broadcast_c.tsup_broadcast_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @sup_broadcast_closed.tsup_broadcast_closed fx0 rc B MT HB MTL cl_record cl_arg_line cl_answer).
Qed.
(* verbs_receive: tverbs_receive_closed (VerbsReceiveClosed.v:108) *)
Lemma cl_verbs_receive : forall fx0 : YK11.FPState,
  @B.Prog.verbs_receive_c.tverbs_receive_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @VerbsReceiveClosed.tverbs_receive_closed fx0 rc B MT RtAPI.PC_STRDUP_RA0 RtAPI.PC_STRNDUP_RA0
  cl_chain_words cl_descriptors_add cl_descriptors_get cl_descriptors_panel_get cl_is_instance_verb
  cl_lv2_refusals_forget cl_number cl_pin_set_words cl_pins_clear cl_reply cl_sup_add cl_sup_after_reply
  cl_sup_broadcast cl_sup_call cl_sup_chain_clear cl_sup_connect cl_sup_host_setting cl_sup_instance_info
  cl_sup_instance_verb cl_sup_lv2_worker_set cl_sup_pin_accept cl_sup_policy_set cl_sup_pool_config
  cl_sup_quarantine_clear cl_sup_remove cl_sup_remove_all cl_sup_reply_code cl_sup_reset cl_sup_resp cl_sup_worker_env
  cl_sup_worker_list cl_verb_is r_sm4 r_sh00 r_shf5 r_shf8 r_strlen r_strcmp r_strncmp r_strcspn r_strtok_r r_atoi
  r_strdup4 r_strndup4 r_free4 HB MTL MTFL).
Qed.
(* send_message: tsend_message_closed (CmdReplyWalksClosed.v:89) *)
Lemma cl_send_message : forall fx0 : YK11.FPState,
  @B.Prog.send_message_c.tsend_message_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @CmdReplyWalksClosed.tsend_message_closed fx0 rc B MT HB MTL MTFL cl_rec_clear cl_verbs_receive
  r_sm1 r_malloc4 r_free4 r_memcpy).
Qed.
(* check_words_add: tcheck_words_add_closed (CheckWordsAddClosed.v:35) *)
Lemma cl_check_words_add : forall fx0 : YK11.FPState,
  @B.Prog.check_words_add_c.tcheck_words_add_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @CheckWordsAddClosed.tcheck_words_add_closed fx0 rc B MT HB r_strcmp r_strncmp). Qed.
(* check_words_chain: tcheck_words_chain_closed (CheckWordsChainClosed.v:36) *)
Lemma cl_check_words_chain : forall fx0 : YK11.FPState,
  @B.Prog.check_words_chain_c.tcheck_words_chain_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @CheckWordsChainClosed.tcheck_words_chain_closed fx0 rc B MT HB r_sm4 r_sh00 r_shf5 r_shf8 r_atoi
  r_snprintf r_strcmp).
Qed.
(* check_words_pin_set: tcwps_closed (CheckWordsPinSetClosed.v:35) *)
Lemma cl_check_words_pin_set : forall fx0 : YK11.FPState,
  @B.Prog.check_words_pin_set_c.tcwps_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @CheckWordsPinSetClosed.tcwps_closed fx0 rc B MT HB r_strcmp r_strncmp). Qed.
(* check_words: tcheck_words_closed (CheckWordsClosed.v:43) *)
Lemma cl_check_words : forall fx0 : YK11.FPState,
  @B.Prog.check_words_c.tcheck_words_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @CheckWordsClosed.tcheck_words_closed fx0 rc B MT HB MTL MTFL cl_joined cl_check_words_add
  cl_check_words_chain cl_check_words_pin_set r_free4 r_sm0 r_strspn r_strcspn r_strcmp r_atoi r_snprintf).
Qed.
(* check_arity: tcheck_arity_closed (CheckArityClosed.v:37) *)
Lemma cl_check_arity : forall fx0 : YK11.FPState,
  @B.Prog.check_arity_c.tcheck_arity_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @CheckArityClosed.tcheck_arity_closed fx0 rc B MT HB r_strcmp r_strcspn r_strncmp r_bcmp).
Qed.
(* check_refusal: tcheck_refusal_closed (CheckRefusalClosed.v:38) *)
Lemma cl_check_refusal : forall fx0 : YK11.FPState,
  @B.Prog.check_refusal_c.tcheck_refusal_spec fx0 rc SK0 PB_cmd B MT.
Proof. exact (fun fx0 => @CheckRefusalClosed.tcheck_refusal_closed fx0 rc B MT HB cl_sup_reply_code). Qed.
(* check_round_trip: tcheck_round_trip_closed (CmdA9ClosedB.v:98) *)
Lemma cl_check_round_trip : forall fx0 : YK11.FPState,
  @B.Prog.check_round_trip_c.tcheck_round_trip_spec fx0 rc SK0 PB_cmd B MT.
Proof.
exact (fun fx0 => @CmdA9ClosedB.tcheck_round_trip_closed fx0 rc B MT HB MTL MTFL cl_send_message cl_joined
  cl_rec_calls_copy cl_rec_calls_equal cl_rec_calls_free RtAPI.PC_STRDUP_RA0 r_free4 r_strdup4 r_strcmp r_sm5 r_sf5
  r_sh00 r_shf8).
Qed.

(** * The entry, and CmdLibX's interface with it *)
(* LLVMFuzzerTestOneInput: tLLVMFuzzerTestOneInput_closed (LLVMFuzzerTestOneInputClosed.v:41); this is
   lib/B/Prog/CmdLibX.v:160's HLTOI *)
Theorem cmd_ltoi_all_B : forall fx0 : YK11.FPState,
  @B.Prog.LLVMFuzzerTestOneInput_c.tLLVMFuzzerTestOneInput_spec fx0 rc YE2k.tfib_sink_head PB_cmd YD2l.CmdB
    YCbp.ameter_triv.
Proof.
exact (fun fx0 => @LLVMFuzzerTestOneInputClosed.tLLVMFuzzerTestOneInput_closed fx0 rc B MT HB MTL MTFL cl_rec_clear
  cl_send_message cl_check_reply cl_check_arity cl_check_words cl_check_refusal cl_check_round_trip r_malloc4 r_free4
  r_memcpy r_strnlen r_strspn r_strcspn).
Qed.
Theorem cmd_lib_x_final_B : forall j : nat,
  @tfib_lib_contract_x_all rc (AgreeShape.ag_shape ZTraceSpec.checksum_shape) YD2l.CmdB YCbp.ameter_triv CmdLibX.XL0
    CmdLibX.XL0 CMD_RLO CMD_RHI GI_cmdA j.
Proof. exact (fun j => @CmdLibX.cmd_lib_x_closed rc cmd_ltoi_all_B j). Qed.
End closed.
