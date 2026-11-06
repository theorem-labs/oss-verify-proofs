(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closing pattern of the statement-pass re-fit for verbs_receive's ASan
   walk (lib/A/Prog/verbs_receive_top.v, tverbs_receive) at the pinned image (lib/A/Prog/CmdImg.v's instance PB_cmd,
   whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head), as SupRemoveAllRefitClosed.v does. The
   record hypotheses come from the A kit (CmdRecImg.v, CmdRecRest.v): IMG is cmd_img_facts_tfib, TL is cmd_palib,
   TLF is cmd_palibf, ML is cmd_model_laws, SIGP is cmd_sig_prog_PB, VOBJS / VHIS are cmd_val_objs_PB /
   cmd_val_his_PB, PRW is cmd_prw_tfib, SMP is cmd_stack_malloc_progress, ASF is cmd_astack_free_law and FFL is
   cmd_frame_flag_law (LAWS is the core's AR_laws_ok, inside verbs_receive_top.v). What remains is the statement's own
   hypotheses (the callees' contracts and the runtime entries), HB, MTL and MTFL. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/VerbsReceiveClosed.v, with its module paths and module names changed; 8 of its 36 lines of code are new or changed and 90 lines of the source are left out. *)
(* The closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F for sup_remove_all's ASan+UBSan walk
   (lib/B/Prog/sup_remove_all.v, tsup_remove_all_spec_holds), mirrored from lib/A/Prog/SupRemoveAllRefitClosed.v: the
   per-binary record hypotheses the walk names, discharged at the pinned image of fuzz_command.asan-ubsan
   (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink head YE2k.tfib_sink_head):
   LAWS is the core's AR_laws_ok, SIGP is cmd_sig_prog_PB, IMG is cmd_img_facts_tfib, and the statement's VOBJS is
   cmd_val_objs_PB (all lib/B/Prog/CmdRecRest.v / CmdRecImg.v). The walk takes neither TL nor PRW. What remains is
   the callees' contracts at every FP state (record, answer), HB and MTL. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require record_c answer_c sup_remove_all_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require sup_remove_all.
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
Theorem tsup_remove_all_closed
  (TRECORD : forall fx0 : YK11.FPState, @record_c.trecord_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT) :
  sup_remove_all_c.tsup_remove_all_spec B MT.
Proof.
exact (sup_remove_all.tsup_remove_all_spec_holds B MT TRECORD TANSWER CmdRecRest.cmd_val_objs_PB HB
  (YG0q.AR_laws_ok SEGS B) MTL CmdRecRest.cmd_sig_prog_PB (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.
End closed.
