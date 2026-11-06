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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require rec_canonical_c arg_line_c arg_line.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Theorem targ_line_closed
  (TREC_CANONICAL : forall fx0 : YK11.FPState,
     @rec_canonical_c.trec_canonical_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (ASTRLEN : forall fx0 : YK11.FPState,
     @astrlen_realizes fx0 rc SEGS B (@pa_sigma _ cmd_listing PB_cmd CS___interceptor_trampoline_strlen)) :
  arg_line_c.targ_line_spec B MT.
Proof.
exact (arg_line.targ_line_holds B MT TREC_CANONICAL ASTRLEN HB MTL CmdRecRest.cmd_val_objs_PB
  CmdRecRest.cmd_sig_prog_PB CmdRecImg.cmd_img_facts_tfib (CmdRecRest.cmd_prw_tfib B HB)).
Qed.
End closed.
Print Assumptions targ_line_closed.
