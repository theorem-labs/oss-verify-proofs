(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closing pattern of the re-fit to statement passes 4-5 for answer's ASan walk
   (lib/A/Prog/answer.v, tanswer_spec_holds), as lib/A/Prog/SupRemoveAllRefitClosed.v does it for the worked example:
   the per-binary record hypotheses the walk names are discharged at the pinned image (lib/A/Prog/CmdImg.v's instance
   PB_cmd, whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head) by the kit's closing helpers: LAWS is
   the core's AR_laws_ok, TL is cmd_palib, TLF is cmd_palibf, ML is cmd_model_laws, SIGP is cmd_sig_prog_PB, VOBJS is
   cmd_val_objs_PB, PRW is cmd_prw_tfib, IMG is cmd_img_facts_tfib, and the two side-stack runtime laws the walk's frame
   steps name are the kit's cmd_stack_malloc_progress (SMP) and cmd_frame_flag_law (FFL). What remains is HB, the
   meter's laws (MTL, and MTFL for the class-7 side-stack frame) and the callees' and runtime entries' contracts at
   every FP state. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/AnswerClosed.v, with its module names changed; 35 of its 63 lines of code are new or changed and 30 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput's ASan walk (lib/A/Prog/LLVMFuzzerTestOneInput.v, pb_LLVMFuzzerTestOneInput) with the
   per-binary hypotheses it names discharged at the pinned image (CmdImg.v's instance PB_cmd, segments tfibsegs, sink
   head AE2k.tfib_sink_head), the closing pattern of the pass-4/5 re-fit (lib/A/Prog/CheckRefusalClosed.v,
   SupRemoveAllRefitClosed.v): LAWS is the core's AR_laws_ok, TL is cmd_palib, IMG is cmd_img_facts_tfib, VOBJS is
   cmd_val_objs_PB, SIGP is cmd_sig_prog_PB, PRW is cmd_prw_tfib, and every byte of g_rec, record.spill and g_quitting
   has an image byte by lib/A/AB13.v's tfib_rom_all. What remains is the statement's own hypotheses (the callees' and
   the runtime entries' contracts at every FP state), HB, and the meter's laws MTL and MTFL. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m AB1v AB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Rt Require Import StrnlenDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj
  CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require rec_clear_c send_message_c check_reply_c
  check_arity_c check_words_c check_refusal_c check_round_trip_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require LLVMFuzzerTestOneInput.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PB_cmd s).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTFL : YC5d.ameter_fs_laws MT.
Theorem tLLVMFuzzerTestOneInput_closed
  (HREC_CLEAR : forall fx0 : YK11.FPState, @rec_clear_c.trec_clear_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (HSEND_MESSAGE : forall fx0 : YK11.FPState, @send_message_c.tsend_message_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (HCHECK_REPLY : forall fx0 : YK11.FPState, @check_reply_c.tcheck_reply_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (HCHECK_ARITY : forall fx0 : YK11.FPState, @check_arity_c.tcheck_arity_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (HCHECK_WORDS : forall fx0 : YK11.FPState, @check_words_c.tcheck_words_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (HCHECK_REFUSAL : forall fx0 : YK11.FPState,
     @check_refusal_c.tcheck_refusal_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (HCHECK_ROUND_TRIP : forall fx0 : YK11.FPState,
     @check_round_trip_c.tcheck_round_trip_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc AE2k.tfib_sink_head SEGS B MT)
  (AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc AE2k.tfib_sink_head SEGS B MT)
  (AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy))
  (AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG CS___asan_memset))
  (ASTRNLEN : forall fx0 : YK11.FPState,
     @astrnlen_whole_realizesM fx0 rc SEGS B 0x10358 0x10378 (SIG CS___interceptor_trampoline_strnlen))
  (ASTRSPN : forall fx0 : YK11.FPState,
     @astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8)
  (ASTRCSPN : forall fx0 : YK11.FPState,
     @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8) :
  LLVMFuzzerTestOneInput_c.tLLVMFuzzerTestOneInput_spec B MT.
Proof.
exact (LLVMFuzzerTestOneInput.pb_LLVMFuzzerTestOneInput B MT HREC_CLEAR HSEND_MESSAGE HCHECK_REPLY HCHECK_ARITY
  HCHECK_WORDS HCHECK_REFUSAL HCHECK_ROUND_TRIP AMALLOC4 AFREE4 AMEMCPY AMEMSET ASTRNLEN ASTRSPN ASTRCSPN HB
  (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palib B HB) (CmdRecImg.cmd_img_facts_tfib B HB) CmdRecRest.cmd_val_objs_PB
  CmdRecRest.cmd_sig_prog_PB (CmdRecRest.cmd_prw_tfib B HB) MTL MTFL CmdRecRest.cmd_prog_rom).
Qed.
End closed.
Print Assumptions tLLVMFuzzerTestOneInput_closed.
