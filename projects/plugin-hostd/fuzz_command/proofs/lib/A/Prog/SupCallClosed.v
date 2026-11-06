(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closing file of the ASan+UBSan walk of arg_line (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan), the pattern of a Theorem Labs lane's PASS4-REFIT.md section F (lib/A/Prog/SupRemoveAllRefitClosed.v,
   a working branch e84227c9553; a Theorem Labs lane's lib/A/Prog/RecBClosed.v, a working branch f349bdaedba): the
   walk's targ_line_holds (lib/B/Prog/arg_line.v) with the per-binary facts it names as Section hypotheses discharged
   at the pinned image (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink head
   YE2k.tfib_sink_head): cmd_val_objs_PB, cmd_sig_prog_PB and PRW (cmd_prw_tfib: the program's statics lie in
   tfibsegs' read-write window) are CmdRecRest's lemmas, cmd_img_facts_tfib is CmdRecImg's. What remains is the
   statement's own hypotheses (rec_canonical's contract and the strlen wrapper's, each at every FP state), HB and
   MTL. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/ArgLineClosed.v, with its module paths and module names changed; 18 of its 42 lines of code are new or changed and 22 lines of the source are left out. *)
(* The closing pattern of the statement-pass re-fit for sup_call's re-fitted
   ASan walk (lib/A/Prog/sup_call.v, tsup_call_holds): the per-binary record hypotheses it names are discharged at the
   pinned image (lib/A/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink head
   AE2k.tfib_sink_head), as the worked example SupRemoveAllRefitClosed.v does: LAWS is the core's AR_laws_ok, TL is
   cmd_palib, SIGP is cmd_sig_prog_PB, VOBJS is cmd_val_objs_PB, IMG is cmd_img_facts_tfib, and PRW is the kit's
   cmd_prw_tfib (the program's statics lie in tfibsegs' read-write window, AB13.v's tfib_rw_window). What remains is
   HB, MTL and the callees' contracts at every FP state. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m AB1v AB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require
rec_calls_free_c arg_i_c arg_line_c answer_c sup_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require sup_call.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Theorem tsup_call_closed
  (TREC_CALLS_FREE : forall fx0 : YK11.FPState,
     @rec_calls_free_c.trec_calls_free_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (TARG_I : forall fx0 : YK11.FPState, @arg_i_c.targ_i_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (TARG_LINE : forall fx0 : YK11.FPState, @arg_line_c.targ_line_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT) :
  sup_call_c.tsup_call_spec B MT.
Proof.
exact (sup_call.tsup_call_holds B MT TREC_CALLS_FREE TARG_I TARG_LINE TANSWER CmdRecRest.cmd_val_objs_PB HB
  (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palib B HB) MTL CmdRecRest.cmd_sig_prog_PB
  (CmdRecImg.cmd_img_facts_tfib B HB) (CmdRecRest.cmd_prw_tfib B HB)).
Qed.
End closed.
Print Assumptions tsup_call_closed.
