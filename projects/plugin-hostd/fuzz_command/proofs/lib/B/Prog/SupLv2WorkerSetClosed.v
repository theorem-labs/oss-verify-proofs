(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the closing of sup_worker_list's ASan+UBSan walk (lib/B/Prog/sup_worker_list.v,
   tsup_worker_list_holds) at the pinned image, after the pattern of a Theorem Labs lane's PASS4-REFIT.md section F
   (lib/A/Prog/SupRemoveAllRefitClosed.v on a working branch e84227c9553). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/SupWorkerListClosed.v, with its module names changed; 13 of its 42 lines of code are new or changed and 10 lines of the source are left out. *)
(* The closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F for sup_lv2_worker_set's ASan+UBSan walk
   (lib/B/Prog/sup_lv2_worker_set.v, tsup_lv2_worker_set_holds; fuzz_command.asan-ubsan): the per-binary record
   hypotheses the walk names are discharged at the pinned image (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments
   are tfibsegs, and the sink head YE2k.tfib_sink_head), as A's SupRemoveAllRefitClosed.v (a working branch e84227c9553)
   and a Theorem Labs lane's RecBClosed.v (a working branch f349bdaedba) do: cmd_img_facts_tfib is a Theorem Labs lane's
   CmdRecImg.cmd_img_facts_tfib, cmd_sig_prog_PB is CmdRecRest.cmd_sig_prog_PB and the statement's VOBJS is
   CmdRecRest.cmd_val_objs_PB; the walk uses no PRW, TL or cmd_val_his_PB, and LAWS is the core's AR_laws_ok inside
   the walk. What remains is the callees' contracts at every FP state, HB and MTL. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require
record_c arg_s_c rec_shape_of_c answer_c sup_lv2_worker_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require sup_lv2_worker_set.
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
Theorem tsup_lv2_worker_set_closed
  (TRECORD : forall fx0 : YK11.FPState, @record_c.trecord_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TARG_S : forall fx0 : YK11.FPState, @arg_s_c.targ_s_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState,
     @rec_shape_of_c.trec_shape_of_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT) :
  sup_lv2_worker_set_c.tsup_lv2_worker_set_spec B MT.
Proof.
exact (@sup_lv2_worker_set.tsup_lv2_worker_set_holds fx rc YE2k.tfib_sink_head PB_cmd B MT
  TRECORD TARG_S TREC_SHAPE_OF TANSWER CmdRecRest.cmd_val_objs_PB HB MTL CmdRecImg.cmd_img_facts_tfib
  CmdRecRest.cmd_sig_prog_PB).
Qed.
End closed.
About tsup_lv2_worker_set_closed.
Print Assumptions tsup_lv2_worker_set_closed.
