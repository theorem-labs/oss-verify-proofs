(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F for descriptors_panel_get's ASan+UBSan walk (lib/B/Prog/descriptors_panel_get.v, tdescriptors_panel_get_holds), in the form of lib/A/Prog/SupRemoveAllRefitClosed.v (a working branch e84227c9553) and a Theorem Labs lane's RecBClosed.v (a working branch f349bdaedba). *)

(* The walk's record facts discharged at the pinned image (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are
   tfibsegs, and B's sink head YE2k.tfib_sink_head): cmd_img_facts_tfib is CmdRecImg's lemma of that name,
   cmd_sig_prog_PB and the statement's VOBJS are CmdRecRest's cmd_sig_prog_PB and cmd_val_objs_PB. What remains is
   the statement's callee contracts (at every FP state), the allocator record HB and the meter's laws MTL. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require
record_c arg_s_c rec_shape_of_c answer_c descriptors_panel_get_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require descriptors_panel_get.
Import ListNotations.
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Theorem tdescriptors_panel_get_closed
  (TRECORD : forall fx0 : YK11.FPState, @record_c.trecord_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TARG_S : forall fx0 : YK11.FPState, @arg_s_c.targ_s_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT) :
  descriptors_panel_get_c.tdescriptors_panel_get_spec B MT.
Proof.
exact (descriptors_panel_get.tdescriptors_panel_get_holds B MT TRECORD TARG_S TREC_SHAPE_OF TANSWER
  CmdRecRest.cmd_val_objs_PB HB CmdRecRest.cmd_sig_prog_PB MTL CmdRecImg.cmd_img_facts_tfib).
Qed.
End closed.
Print Assumptions descriptors_panel_get.tdescriptors_panel_get_holds.
Print Assumptions tdescriptors_panel_get_closed.
