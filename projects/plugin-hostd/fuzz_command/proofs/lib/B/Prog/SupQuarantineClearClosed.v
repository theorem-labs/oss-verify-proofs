(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the closing corollary of sup_quarantine_clear's ASan+UBSan walk
   (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan), in the pattern of a Theorem Labs lane's PASS4-REFIT.md section F
   (lib/A/Prog/SupRemoveAllRefitClosed.v; a Theorem Labs lane's RecBClosed.v): the walk's theorem
   (lib/B/Prog/sup_quarantine_clear.v, tsup_quarantine_clear_holds) at the pinned image (lib/B/Prog/CmdImg.v's
   instance PB_cmd, whose segments are B's tfibsegs, and B's sink head YE2k.tfib_sink_head), with the facts a Theorem Labs lane
   states there discharged by its lemmas: the object bridge is cmd_val_objs_PB, the call targets cmd_sig_prog_PB
   (lib/B/Prog/CmdRecRest.v), the image facts cmd_img_facts_tfib (lib/B/Prog/CmdRecImg.v). What remains is the
   statement's callee contracts (each at every FP state), the allocator record HB and the meter's laws MTL. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require
record_c arg_s_c rec_shape_of_c answer_c sup_quarantine_clear_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require sup_quarantine_clear.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Theorem tsup_quarantine_clear_closed
  (TRECORD : forall fx0 : YK11.FPState, @record_c.trecord_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TARG_S : forall fx0 : YK11.FPState, @arg_s_c.targ_s_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT) :
  @sup_quarantine_clear_c.tsup_quarantine_clear_spec fx rc YE2k.tfib_sink_head PB_cmd B MT.
Proof.
exact (@sup_quarantine_clear.tsup_quarantine_clear_holds fx rc YE2k.tfib_sink_head PB_cmd B MT
  TRECORD TARG_S TREC_SHAPE_OF TANSWER (CmdRecRest.cmd_val_objs_PB (rc := rc)) HB MTL
  (CmdRecRest.cmd_sig_prog_PB (rc := rc)) CmdRecImg.cmd_img_facts_tfib).
Qed.
End closed.

Set Printing Width 4000.
About tsup_quarantine_clear_closed.
Print Assumptions tsup_quarantine_clear_closed.
