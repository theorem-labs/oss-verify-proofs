(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closing file of mix_call's ASan+UBSan walk (lib/B/Prog/mix_call.v,
   tmix_call_spec_holds), in the closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F (the A model:
   lib/A/Prog/SupRemoveAllRefitClosed.v on a working branch e84227c9553): the walk's Section hypotheses are discharged at
   the pinned image, the instance PB_cmd of a Theorem Labs lane's lib/B/Prog/CmdImg.v (whose segments are a Theorem Labs lane's tfibsegs) and
   the sink head YE2k.tfib_sink_head, both given by name: VOBJS is CmdRecRest's cmd_val_objs_PB and the image facts
   are CmdRecImg's cmd_img_facts_tfib. What remains is the allocator record HB and the statement's runtime entry
   ASTRLEN (the strlen wrapper's contract at every FP state). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdImg CmdRecImg CmdRecRest mix_call_c mix_call.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing CmdImg.PB_cmd).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Theorem tmix_call_closed
  (ASTRLEN : forall fx0 : YK11.FPState,
     @astrlen_realizes fx0 rc SEGS B (@pa_sigma _ cmd_listing CmdImg.PB_cmd CS___interceptor_trampoline_strlen)) :
  @mix_call_c.tmix_call_spec fx rc YE2k.tfib_sink_head CmdImg.PB_cmd B MT.
Proof.
exact (@mix_call.tmix_call_spec_holds fx rc YE2k.tfib_sink_head CmdImg.PB_cmd B MT ASTRLEN
  CmdRecRest.cmd_val_objs_PB HB CmdRecImg.cmd_img_facts_tfib).
Qed.
End closed.
About tmix_call_closed.
Print Assumptions tmix_call_closed.
