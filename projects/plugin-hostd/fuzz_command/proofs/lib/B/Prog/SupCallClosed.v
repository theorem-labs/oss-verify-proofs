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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/AnswerClosed.v, with its module paths, module names and addresses changed; 20 of its 48 lines of code are new or changed and 30 lines of the source are left out. *)
(* The closing pattern of the statement-pass re-fit for sup_call's B walk (lib/B/Prog/sup_call.v,
   tsup_call_spec_holds): the walk hypotheses discharged at the pinned image (lib/B/Prog/CmdImg.v's instance PB_cmd,
   whose segments are tfibsegs, and the sink head YE2k.tfib_sink_head), every one by a kit lemma:
   - LAWS is the core's AR_laws_ok; TL is cmd_palib, TLF cmd_palibf, SIGP cmd_sig_prog_PB, IMG cmd_img_facts_tfib,
     ML cmd_model_laws, SMP cmd_stack_malloc_progress, ASF cmd_astack_free_law, FFL cmd_frame_flag_law, and the
     statement's VOBJS cmd_val_objs_PB (lib/B/Prog/CmdRecRest.v, CmdRecImg.v).
   What remains: the statement's callee and runtime contracts (in their `forall fx0` form), HB, MTL and MTFL. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaLibF CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c arg_line_c answer_c sup_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require sup_call.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PB_cmd c).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws; the side-stack frame needs the
   meter's frame laws (MTFL) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTFL : YC5d.ameter_fs_laws MT.

Theorem tsup_call_closed
  (TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0)
  (ASNPRINTF : forall fx0 : YK11.FPState,
     @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158) :
  tsup_call_spec B MT.
Proof.
eapply (@sup_call.tsup_call_spec_holds fx rc YE2k.tfib_sink_head PB_cmd B MT);
first [ exact TRECORD | exact TARG_S | exact TARG_LINE | exact TANSWER | exact ASTACK_MALLOC0 | exact ASNPRINTF
      | exact cmd_val_objs_PB | exact HB | exact (YG0q.AR_laws_ok SEGS B) | exact (cmd_palib B HB)
      | exact (cmd_palibf B HB) | exact (cmd_model_laws B HB) | exact (cmd_stack_malloc_progress B) | exact MTL
      | exact MTFL | exact (cmd_astack_free_law B) | exact (cmd_frame_flag_law B)
      | exact cmd_sig_prog_PB | exact (cmd_img_facts_tfib B HB) ].
Qed.
End closed.
