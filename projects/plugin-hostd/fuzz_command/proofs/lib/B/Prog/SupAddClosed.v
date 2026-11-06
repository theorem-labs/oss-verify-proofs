(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closing pattern of the re-fit to statement passes 4-5 for answer's ASan walk
   (lib/A/Prog/answer.v, tanswer_spec_holds), as lib/A/Prog/SupRemoveAllRefitClosed.v does it for the worked example:
   the per-binary record hypotheses the walk names are discharged at the pinned image (lib/A/Prog/CmdImg.v's instance
   PB_cmd, whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head) by the kit's closing helpers: LAWS is
   the core's AR_laws_ok, TL is cmd_palib, TLF is cmd_palibf, ML is cmd_model_laws, SIGP is cmd_sig_prog_PB, VOBJS is
   cmd_val_objs_PB, PRW is cmd_prw_tfib, IMG is cmd_img_facts_tfib, and the two side-stack runtime laws the walk's frame
   steps name are the kit's cmd_stack_malloc_progress (SMP) and cmd_frame_flag_law (FFL). What remains is HB, the
   meter's laws (MTL, and MTFL for the class-7 side-stack frame) and the callees' and runtime entries' contracts at
   every FP state. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/AnswerClosed.v, with its module paths, module names and addresses changed; 18 of its 49 lines of code are new or changed and 27 lines of the source are left out. *)
(* The closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F for sup_add's ASan+UBSan walk (lib/B/Prog/sup_add.v,
   sup_add_holds): the per-binary record hypotheses it names discharged at the pinned image (lib/B/Prog/CmdImg.v's
   instance PB_cmd, whose segments are tfibsegs, and the sink head YE2k.tfib_sink_head), as A's worked example
   lib/A/Prog/SupRemoveAllRefitClosed.v and a Theorem Labs lane's RecBClosed.v (a working branch
   f349bdaedba) do, each by the B kit's lemma (lib/B/Prog/CmdRecRest.v, CmdRecImg.v): LAWS is the core's AR_laws_ok,
   TL is cmd_palib, TLF is cmd_palibf, ML is cmd_model_laws, SMP is cmd_stack_malloc_progress, ASF is
   cmd_astack_free_law, FFL is cmd_frame_flag_law, SIGP is cmd_sig_prog_PB, PRW is cmd_prw_tfib, IMG is
   cmd_img_facts_tfib and VOBJS is cmd_val_objs_PB. What remains is the statement's own hypotheses (the callees' and
   runtime entries' contracts at every FP state), HB and the meter's laws MTL and MTFL. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib CmdRecFacts CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg CmdRecRest PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require
record_c arg_s_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require sup_add.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PB_cmd s).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTFL : YC5d.ameter_fs_laws MT.
Theorem tsup_add_closed
  (TRECORD : forall fx0 : YK11.FPState, @record_c.trecord_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TARG_S : forall fx0 : YK11.FPState, @arg_s_c.targ_s_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TMIX_CALL : forall fx0 : YK11.FPState, @mix_call_c.tmix_call_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (THAND_BACK : forall fx0 : YK11.FPState, @hand_back_c.thand_back_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (ASTACK_MALLOC1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1)
  (ASNPRINTF : forall fx0 : YK11.FPState,
     @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158) :
  sup_add_c.tsup_add_spec B MT.
Proof.
exact (sup_add.sup_add_holds B MT HB (CmdRecRest.cmd_palib B HB) (CmdRecRest.cmd_palibf B HB)
  (CmdRecRest.cmd_model_laws B HB) (CmdRecRest.cmd_stack_malloc_progress B) MTL MTFL
  (CmdRecRest.cmd_astack_free_law B) (CmdRecRest.cmd_frame_flag_law B) CmdRecRest.cmd_sig_prog_PB
  (CmdRecRest.cmd_prw_tfib B HB) (CmdRecImg.cmd_img_facts_tfib B HB) TRECORD TARG_S TMIX_CALL THAND_BACK TANSWER
  ASTACK_MALLOC1 ASNPRINTF CmdRecRest.cmd_val_objs_PB).
Qed.
End closed.
Print Assumptions tsup_add_closed.
