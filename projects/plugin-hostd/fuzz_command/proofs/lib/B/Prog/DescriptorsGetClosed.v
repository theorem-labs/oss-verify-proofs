(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F for descriptors_get's
   ASan+UBSan walk (lib/B/Prog/descriptors_get.v, tdescriptors_get_holds), modelled on lib/A/Prog/RecBClosed.v
   (a working branch f349bdaedba, :163-191) and lib/A/Prog/SupRemoveAllRefitClosed.v (a working branch
   e84227c9553, :50-60). *)

(* descriptors_get's walk at the pinned image: lib/B/Prog/CmdImg.v's instance PB_cmd (segments tfibsegs) and the sink
   head YE2k.tfib_sink_head. The walk's per-binary hypotheses are discharged by a Theorem Labs lane's record facts: VOBJS by
   CmdRecRest.cmd_val_objs_PB, cmd_sig_prog_PB by CmdRecRest.cmd_sig_prog_PB, cmd_img_facts_tfib by
   CmdRecImg.cmd_img_facts_tfib. What remains is the statement's own callee contracts (at every FP state), the
   allocator record HB and the meter's laws MTL. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require
record_c arg_s_c rec_shape_of_c answer_c descriptors_get_c descriptors_get.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
Variable B : YG0f.asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Theorem tdescriptors_get_closed
  (TRECORD : forall fx0 : YK11.FPState, @record_c.trecord_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TARG_S : forall fx0 : YK11.FPState, @arg_s_c.targ_s_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState,
     @rec_shape_of_c.trec_shape_of_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT) :
  descriptors_get_c.tdescriptors_get_spec B MT.
Proof.
exact (descriptors_get.tdescriptors_get_holds B MT TRECORD TARG_S TREC_SHAPE_OF TANSWER CmdRecRest.cmd_val_objs_PB
  HB MTL CmdRecRest.cmd_sig_prog_PB CmdRecImg.cmd_img_facts_tfib).
Qed.
End closed.
