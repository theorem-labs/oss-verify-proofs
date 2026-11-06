(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the closing of sup_reset's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan; lib/B/Prog/sup_reset.v, tsup_reset_holds) at the pinned image: lib/B/Prog/CmdImg.v's
   instance PB_cmd, whose segments are tfibsegs, and the sink head YE2k.tfib_sink_head. The pattern of
   a Theorem Labs lane's PASS4-REFIT.md section F (A's lib/A/Prog/SupRemoveAllRefitClosed.v:50-60 on a working branch e84227c9553,
   a Theorem Labs lane's lib/A/Prog/RecBClosed.v:163-191 on a working branch f349bdaedba), with a Theorem Labs lane's B
   CmdRecFacts (a working branch fc8bcbd8b42): the walk's per-binary image facts are CmdRecImg.cmd_img_facts_tfib, its
   object bridge is CmdRecRest.cmd_val_objs_PB and its call targets are CmdRecRest.cmd_sig_prog_PB. The walk names no
   PALib (no inline check) and no program-static write (no PRW). What remains is the allocator record HB, the meter's
   laws MTL and the four callee contracts at every FP state. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require
record_c arg_s_c rec_shape_of_c answer_c sup_reset_c sup_reset.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Theorem tsup_reset_closed
  (TRECORD : forall fx0 : YK11.FPState, @record_c.trecord_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TARG_S : forall fx0 : YK11.FPState, @arg_s_c.targ_s_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT) :
  @sup_reset_c.tsup_reset_spec fx rc YE2k.tfib_sink_head PB_cmd B MT.
Proof.
exact (@sup_reset.tsup_reset_holds fx rc YE2k.tfib_sink_head PB_cmd B MT TRECORD TARG_S TREC_SHAPE_OF TANSWER
  CmdRecRest.cmd_val_objs_PB HB MTL CmdRecRest.cmd_sig_prog_PB CmdRecImg.cmd_img_facts_tfib).
Qed.
End closed.

Print Assumptions tsup_reset_closed.
