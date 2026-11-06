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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/AnswerClosed.v, with its module names changed; 16 of its 46 lines of code are new or changed and 28 lines of the source are left out. *)
(* The closing pattern of the re-fit to statement passes 4-5 for arg_i's re-fitted ASan walk (lib/A/Prog/arg_i.v,
   targ_i_spec_holds): the per-binary record hypotheses it names are discharged at the pinned image
   (lib/A/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head) by the
   kit's closers, as lib/A/Prog/SupRemoveAllRefitClosed.v does: LAWS is the core's AR_laws_ok, TL is cmd_palib, TLF is
   cmd_palibf, ML is cmd_model_laws, SIGP is cmd_sig_prog_PB, VOBJS is cmd_val_objs_PB, PRW is cmd_prw_tfib, IMG is
   cmd_img_facts_tfib, and the side-stack frame's laws SMP, FFL and ASF are cmd_stack_malloc_progress,
   cmd_frame_flag_law and cmd_astack_free_law (CmdRecRest / CmdRecImg). What remains is HB, the meter's laws (MTL,
   MTFL: the side-stack frame changes the meter's frame state), and the callee's and the runtime entries' contracts
   at every FP state. arg_i, arg_i_c and xstrdup_c are named by their full paths: the plain proofs' modules of the
   same names (lib/Prog) are loaded too. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m AB1v AB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require xstrdup_c arg_i_c arg_i.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PB_cmd c).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTFL : YC5d.ameter_fs_laws MT.
Theorem targ_i_closed
  (TXSTRDUP : forall fx0 : YK11.FPState,
     @OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.xstrdup_c.txstrdup_spec
       fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0)
  (ASNPRINTF : forall fx0 : YK11.FPState,
     @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8) :
  OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.arg_i_c.targ_i_spec B MT.
Proof.
exact (OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog.arg_i.targ_i_spec_holds B MT
  HB (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palib B HB) (CmdRecRest.cmd_palibf B HB)
  (CmdRecRest.cmd_model_laws B HB) (CmdRecRest.cmd_stack_malloc_progress B) MTL MTFL
  (CmdRecRest.cmd_astack_free_law B) (CmdRecRest.cmd_frame_flag_law B) CmdRecRest.cmd_sig_prog_PB
  (CmdRecRest.cmd_prw_tfib B HB) (CmdRecImg.cmd_img_facts_tfib B HB) TXSTRDUP ASTACK_MALLOC0 ASNPRINTF
  CmdRecRest.cmd_val_objs_PB).
Qed.
End closed.
