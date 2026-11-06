(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the closing of sup_after_reply's ASan+UBSan walk (lib/B/Prog/sup_after_reply.v,
   tsup_after_reply_holds) at the pinned image (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs,
   and the sink head YE2k.tfib_sink_head), as a Theorem Labs lane's PASS4-REFIT.md section F describes: VOBJS is cmd_val_objs_PB,
   TL is cmd_palib, TLF is cmd_palibf, SIGP is cmd_sig_prog_PB, the image facts are cmd_img_facts_tfib, the frame
   flag law is cmd_frame_flag_law and the stack free law is cmd_astack_free_law (a Theorem Labs lane's lib/B/Prog/CmdRecRest.v and
   CmdRecImg.v). What remains is HB, MTL, MTLF and the callee and runtime contracts at every FP state. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib CmdRecFacts PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require record_c arg_s_c sup_after_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require sup_after_reply.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTLF : YC5d.ameter_fs_laws MT.
Theorem tsup_after_reply_closed
  (TRECORD : forall fx0 : YK11.FPState, @record_c.trecord_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TARG_S : forall fx0 : YK11.FPState, @arg_s_c.targ_s_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0)
  (ASNPRINTF : forall fx0 : YK11.FPState,
     @asnprintf_realizes fx0 rc SEGS B (@pa_sigma _ cmd_listing PB_cmd CS___interceptor_trampoline_snprintf)
       0xa6bf8 0x604158) :
  @sup_after_reply_c.tsup_after_reply_spec fx rc YE2k.tfib_sink_head PB_cmd B MT.
Proof.
exact (@sup_after_reply.tsup_after_reply_holds fx rc YE2k.tfib_sink_head PB_cmd B MT TRECORD TARG_S ASTACK_MALLOC0
  (CmdRecRest.cmd_astack_free_law B)
  ASNPRINTF CmdRecRest.cmd_val_objs_PB HB (CmdRecRest.cmd_palib B HB) (CmdRecRest.cmd_palibf B HB) MTL MTLF
  CmdRecRest.cmd_sig_prog_PB CmdRecImg.cmd_img_facts_tfib (CmdRecRest.cmd_frame_flag_law B)).
Qed.
End closed.
About tsup_after_reply_closed.
Print Assumptions tsup_after_reply_closed.
