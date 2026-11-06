(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F for record's ASan+UBSan
   walk (lib/B/Prog/record.v, trecord_holds) on fuzz_command.asan-ubsan: the walk's per-binary hypotheses discharged
   at the pinned image (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are B's tfibsegs, and the sink head
   YE2k.tfib_sink_head), after A's lib/A/Prog/SupRemoveAllRefitClosed.v (a working branch e84227c9553) and
   RecBClosed.v (a working branch f349bdaedba): VOBJS is CmdRecRest.v cmd_val_objs_PB, cmd_sig_prog_PB is
   CmdRecRest.v cmd_sig_prog_PB, cmd_img_facts_tfib is CmdRecImg.v cmd_img_facts_tfib, and PRW is CmdRecRest.v
   cmd_prw_tfib (the program's statics lie in tfibsegs' read-write window). What remains is the statement's callee
   contract (rec_calls_free at every FP state), HB and MTL. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require record.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require rec_calls_free_c record_c.
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
Theorem trecord_closed
  (TREC_CALLS_FREE : forall fx0 : YK11.FPState,
     @rec_calls_free_c.trec_calls_free_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT) :
  record_c.trecord_spec B MT.
Proof.
exact (record.trecord_holds B MT TREC_CALLS_FREE CmdRecRest.cmd_val_objs_PB HB MTL CmdRecRest.cmd_sig_prog_PB
  (CmdRecRest.cmd_prw_tfib B HB) CmdRecImg.cmd_img_facts_tfib).
Qed.
End closed.
About trecord_closed.
Print Assumptions trecord_closed.
Print Assumptions record.trecord_holds.
