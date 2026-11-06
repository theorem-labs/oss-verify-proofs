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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/AnswerClosed.v, with its module paths and module names changed; 37 of its 58 lines of code are new or changed and 37 lines of the source are left out. *)
(* The closing file of sup_instance_verb's ASan+UBSan walk (plugin-hostd/fuzz_command, image fuzz_command.asan-ubsan),
   in the pattern of a Theorem Labs lane's PASS4-REFIT.md section F: the walk's theorem (lib/B/Prog/sup_instance_verb.v,
   tsup_instance_verb_holds) at the pinned image (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are
   tfibsegs, and B's sink head YE2k.tfib_sink_head), with the per-binary facts that its Section names discharged by
   the Theorem Labs lane lemmas of the same names, as A's SupRemoveAllRefitClosed.v (a working branch e84227c9553) does for
   sup_remove_all: cmd_img_facts_tfib (CmdRecImg), cmd_palib, cmd_sig_prog_PB, the PALibF record (cmd_palibf, the
   walk's TLF), the side-stack frames' flag law (cmd_frame_flag_law, the walk's FFL), the astack free law
   (cmd_astack_free_law, the statement's AFREE_LAW) and the object bridge (cmd_val_objs_PB, the statement's VOBJS)
   (CmdRecRest), as a working branch's SupAfterReplyClosed.v does. What remains is the callees' and
   runtime entries' contracts at every FP state, HB and the meter's laws MTL and MTLF. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdImg CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require
record_c arg_line_c arg_s_c rec_shape_of_c answer_c sup_instance_verb_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require sup_instance_verb.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PB_cmd s).
Variable B : asyms.
Variable MT : ameter_ops.
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1); MTLF carries the meter across the
   side-stack frame's set_fs *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTLF : ameter_fs_laws MT.
Theorem tsup_instance_verb_closed
  (TRECORD : forall fx0 : YK11.FPState, @record_c.trecord_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TARG_LINE : forall fx0 : YK11.FPState, @arg_line_c.targ_line_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TARG_S : forall fx0 : YK11.FPState, @arg_s_c.targ_s_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState,
     @rec_shape_of_c.trec_shape_of_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0)
  (ASNPRINTF : forall fx0 : YK11.FPState,
     @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158)
  (ASTRSPN : forall fx0 : YK11.FPState,
     @astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa6bf8 0x604158)
  (ASTRCSPN : forall fx0 : YK11.FPState,
     @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158) :
  sup_instance_verb_c.tsup_instance_verb_spec (fx := fx) (rc := rc) (SK := YE2k.tfib_sink_head) (PI := PB_cmd) B MT.
Proof.
(* the walk's pinned-image hypotheses, under the walk's Section names *)
pose proof CmdRecImg.cmd_img_facts_tfib as cmd_img_facts_tfib.
pose proof (CmdRecRest.cmd_palib B HB) as cmd_palib.
pose proof CmdRecRest.cmd_sig_prog_PB as cmd_sig_prog_PB.
pose proof (CmdRecRest.cmd_palibf B HB) as TLF.
pose proof (CmdRecRest.cmd_frame_flag_law B) as FFL.
pose proof (CmdRecRest.cmd_astack_free_law B) as AFREE_LAW.
pose proof CmdRecRest.cmd_val_objs_PB as VOBJS.
(* the walk theorem's arguments after B MT, in its Section order (`About sup_instance_verb.tsup_instance_verb_holds`) *)
exact (sup_instance_verb.tsup_instance_verb_holds (fx := fx) (rc := rc) (SK := YE2k.tfib_sink_head) (PI := PB_cmd) B MT
  TRECORD TARG_LINE TARG_S TREC_SHAPE_OF TANSWER ASTACK_MALLOC0 AFREE_LAW ASNPRINTF ASTRSPN ASTRCSPN VOBJS HB cmd_img_facts_tfib cmd_palib cmd_sig_prog_PB TLF FFL MTL MTLF).
Qed.
End closed.
About tsup_instance_verb_closed.
Print Assumptions tsup_instance_verb_closed.
