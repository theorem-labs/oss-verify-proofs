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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/SupPoolConfigClosed.v, with its module names changed; 16 of its 51 lines of code are new or changed and 23 lines of the source are left out. *)
(* The closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F for sup_instance_info's ASan+UBSan walk
   (lib/B/Prog/sup_instance_info.v, tsup_instance_info_holds): the per-binary facts the walk names as Section
   hypotheses are discharged at the pinned image (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are B's
   tfibsegs, and B's sink head YE2k.tfib_sink_head), as a Theorem Labs lane's RecBClosed.v (a working branch
   f349bdaedba, lib/A/Prog/RecBClosed.v:163-191) and a Theorem Labs lane's SupRemoveAllRefitClosed.v (a working branch e84227c9553) do
   on the ASan side, each by a Theorem Labs lane's lemma of that name (lib/B/Prog/CmdRecRest.v, CmdRecImg.v at a working branch
   707acd856cb): IMG is cmd_img_facts_tfib, TL cmd_palib, TLF cmd_palibf, the frame flag law cmd_frame_flag_law,
   cmd_sig_prog_PB itself, the statement's VOBJS cmd_val_objs_PB and its AFREE_LAW (the side-stack free law)
   cmd_astack_free_law; LAWS is the core's AR_laws_ok inside the walk. What remains is the statement's own callee
   and runtime contracts (at every FP state), HB, MTL and MTLF. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg CmdRecRest PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require
record_c arg_s_c rec_shape_of_c answer_c sup_instance_info_c sup_instance_info.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1; MTLF: cgif's MLAWF) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTLF : YC5d.ameter_fs_laws MT.
Theorem tsup_instance_info_closed
  (TRECORD : forall fx0 : YK11.FPState, @record_c.trecord_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TARG_S : forall fx0 : YK11.FPState, @arg_s_c.targ_s_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState,
     @rec_shape_of_c.trec_shape_of_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0)
  (ASNPRINTF : forall fx0 : YK11.FPState,
     @RtFormat.asnprintf_realizes fx0 rc SEGS B (@pa_sigma _ cmd_listing PB_cmd CS___interceptor_trampoline_snprintf)
       0xa6bf8 0x604158) :
  @sup_instance_info_c.tsup_instance_info_spec fx rc YE2k.tfib_sink_head PB_cmd B MT.
Proof.
pose proof (@CmdRecRest.cmd_val_objs_PB rc) as VOBJS.
pose proof (@CmdRecRest.cmd_astack_free_law rc B) as AFREE_LAW.
pose proof (@CmdRecRest.cmd_palib rc B HB) as TL.
pose proof (CmdRecRest.cmd_palibf (rc := rc) B HB) as TLF.
pose proof (@CmdRecRest.cmd_sig_prog_PB rc) as SIGP.
pose proof CmdRecImg.cmd_img_facts_tfib as IMGT.
pose proof (@CmdRecRest.cmd_frame_flag_law rc) as FFL.
apply (@sup_instance_info.tsup_instance_info_holds fx rc YE2k.tfib_sink_head PB_cmd B MT); assumption.
Qed.
End closed.
Print Assumptions tsup_instance_info_closed.
About tsup_instance_info_closed.
