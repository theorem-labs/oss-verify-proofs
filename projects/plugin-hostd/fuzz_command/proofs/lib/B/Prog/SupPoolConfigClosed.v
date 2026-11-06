(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the closing of sup_pool_config's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan; lib/B/Prog/sup_pool_config.v, tsup_pool_config_holds) at the pinned image:
   lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink head YE2k.tfib_sink_head. The
   pattern of a Theorem Labs lane's PASS4-REFIT.md section F, as lib/B/Prog/SupResetClosed.v and lib/B/Prog/AnswerCodeClosed.v
   close theirs, with a Theorem Labs lane's B CmdRecFacts (a working branch 707acd856cb): the image facts are
   CmdRecImg.cmd_img_facts_tfib; the statement's VOBJS is CmdRecRest.cmd_val_objs_PB and its AFREE_LAW (the side-stack
   free law, astack_free_law) is CmdRecRest.cmd_astack_free_law; the walk's call targets, runtime pcs and shadow
   cells, side-stack pcs and use-after-return cells, and frame flag law are CmdRecRest.cmd_sig_prog_PB, cmd_palib,
   cmd_palibf and cmd_frame_flag_law. What remains is the allocator record HB, the meter's laws MTL and MTLF, and the
   statement's callee and runtime contracts at every FP state. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRest PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require
record_c arg_s_c rec_shape_of_c answer_c sup_pool_config_c sup_pool_config.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1; MTLF: the side-stack form) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTLF : YC5d.ameter_fs_laws MT.
Theorem tsup_pool_config_closed
  (TRECORD : forall fx0 : YK11.FPState, @record_c.trecord_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TARG_S : forall fx0 : YK11.FPState, @arg_s_c.targ_s_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0)
  (ASNPRINTF : forall fx0 : YK11.FPState,
     @RtFormat.asnprintf_realizes fx0 rc SEGS B (@pa_sigma _ cmd_listing PB_cmd CS___interceptor_trampoline_snprintf)
       0xa6bf8 0x604158) :
  @sup_pool_config_c.tsup_pool_config_spec fx rc YE2k.tfib_sink_head PB_cmd B MT.
Proof.
eapply (@sup_pool_config.tsup_pool_config_holds fx rc YE2k.tfib_sink_head PB_cmd B MT).
all: first
  [ exact TRECORD | exact TARG_S | exact TREC_SHAPE_OF | exact TANSWER | exact ASTACK_MALLOC0
  | exact ASNPRINTF | exact (@CmdRecRest.cmd_val_objs_PB rc) | exact HB | exact MTL | exact MTLF
  | exact (@CmdRecRest.cmd_sig_prog_PB rc) | exact (@CmdRecRest.cmd_palib rc) | exact CmdRecRest.cmd_palibf
  | exact CmdRecRest.cmd_frame_flag_law | exact (CmdRecRest.cmd_astack_free_law B)
  | exact CmdRecImg.cmd_img_facts_tfib ].
Qed.
End closed.

About tsup_pool_config_closed.
Print Assumptions tsup_pool_config_closed.
