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
(* The closing pattern of the statement-pass re-fit for sup_resp's re-fitted ASan walk (lib/A/Prog/sup_resp.v,
   tsup_resp_spec_holds): the per-binary record hypotheses it names are discharged at the pinned image
   (lib/A/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head), as
   lib/A/Prog/SupRemoveAllRefitClosed.v does: LAWS is the core's AR_laws_ok, TL is cmd_palib, TLF is cmd_palibf, ML
   is cmd_model_laws, SIGP is cmd_sig_prog_PB, VOBJS is cmd_val_objs_PB and IMG is cmd_img_facts_tfib, and the
   side-stack frame's laws SMP, ASF and FFL are cmd_stack_malloc_progress, cmd_astack_free_law and cmd_frame_flag_law
   (the kit's CmdRecRest / CmdRecImg). What remains is HB, the meter's laws (MTL, MTFL: the side-stack frame changes
   the meter's frame state) and the callee's and the runtime entries' contracts at every FP state. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecImg CmdRecRest PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require xstrdup_c sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require sup_resp.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
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
Theorem tsup_resp_closed
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (ASTACK_MALLOC1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1)
  (ASNPRINTF : forall fx0 : YK11.FPState,
     @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8) :
  sup_resp_c.tsup_resp_spec B MT.
Proof.
apply (sup_resp.tsup_resp_spec_holds B MT); first
  [ exact TXSTRDUP | exact ASTACK_MALLOC1 | exact ASNPRINTF | exact CmdRecRest.cmd_val_objs_PB | exact HB
  | exact (YG0q.AR_laws_ok SEGS B) | exact (CmdRecRest.cmd_palib B HB) | exact (CmdRecRest.cmd_palibf B HB)
  | exact (CmdRecRest.cmd_model_laws B HB) | exact (CmdRecRest.cmd_stack_malloc_progress B)
  | exact MTL | exact MTFL | exact (CmdRecRest.cmd_astack_free_law B) | exact (CmdRecRest.cmd_frame_flag_law B)
  | exact CmdRecRest.cmd_sig_prog_PB | exact (CmdRecImg.cmd_img_facts_tfib B HB) ].
Qed.
End closed.
Print Assumptions tsup_resp_closed.
