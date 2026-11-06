(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the closing of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, lib/B/Prog/LLVMFuzzerTestOneInput.v tLLVMFuzzerTestOneInput_holds) at the pinned image (lib/B/Prog/CmdImg.v's PB_cmd, segments tfibsegs, sink head YE2k.tfib_sink_head), in the form of lib/A/Prog/SupRemoveAllRefitClosed.v (a Theorem Labs lane's PASS4-REFIT.md section F): LAWS is the core's AR_laws_ok, TL is cmd_palib, SIGP is cmd_sig_prog_PB, IMG is cmd_img_facts_tfib, VOBJS is cmd_val_objs_PB, PRW is the kit's cmd_prw_tfib and segment E's cmd_prog_rd is the kit's cmd_prog_rom (lib/B/Prog/CmdRecRest.v). What remains is the statement's own hypotheses (the callees' and the runtime entries' contracts at every FP state), HB, MTL and MTFL. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m YB1v YB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Rt Require Import StrnlenDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj
  CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require rec_clear_c send_message_c check_reply_c
  check_arity_c check_words_c check_refusal_c check_round_trip_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require LLVMFuzzerTestOneInput.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PB_cmd s).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Theorem tLLVMFuzzerTestOneInput_closed
  (HREC_CLEAR : forall fx0 : YK11.FPState, @rec_clear_c.trec_clear_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (HSEND_MESSAGE : forall fx0 : YK11.FPState, @send_message_c.tsend_message_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (HCHECK_REPLY : forall fx0 : YK11.FPState, @check_reply_c.tcheck_reply_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (HCHECK_ARITY : forall fx0 : YK11.FPState, @check_arity_c.tcheck_arity_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (HCHECK_WORDS : forall fx0 : YK11.FPState, @check_words_c.tcheck_words_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (HCHECK_REFUSAL : forall fx0 : YK11.FPState,
     @check_refusal_c.tcheck_refusal_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (HCHECK_ROUND_TRIP : forall fx0 : YK11.FPState,
     @check_round_trip_c.tcheck_round_trip_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc YE2k.tfib_sink_head SEGS B MT)
  (AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc YE2k.tfib_sink_head SEGS B MT)
  (AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy))
  (ASTRNLEN : forall fx0 : YK11.FPState,
     @astrnlen_whole_realizesM fx0 rc SEGS B 0x10358 0x10378 (SIG CS___interceptor_trampoline_strnlen))
  (ASTRSPN : forall fx0 : YK11.FPState,
     @astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa6bf8 0x604158)
  (ASTRCSPN : forall fx0 : YK11.FPState,
     @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158) :
  LLVMFuzzerTestOneInput_c.tLLVMFuzzerTestOneInput_spec B MT.
Proof.
exact (LLVMFuzzerTestOneInput.tLLVMFuzzerTestOneInput_holds B MT HREC_CLEAR HSEND_MESSAGE HCHECK_REPLY HCHECK_ARITY
  HCHECK_WORDS HCHECK_REFUSAL HCHECK_ROUND_TRIP AMALLOC4 AFREE4 AMEMCPY ASTRNLEN ASTRSPN ASTRCSPN
  (YG0q.AR_laws_ok SEGS B) HB (CmdRecRest.cmd_palib B HB) (CmdRecImg.cmd_img_facts_tfib B HB)
  CmdRecRest.cmd_val_objs_PB CmdRecRest.cmd_sig_prog_PB (CmdRecRest.cmd_prw_tfib B HB) MTL MTFL
  CmdRecRest.cmd_prog_rom).
Qed.
End closed.
Print Assumptions tLLVMFuzzerTestOneInput_closed.
