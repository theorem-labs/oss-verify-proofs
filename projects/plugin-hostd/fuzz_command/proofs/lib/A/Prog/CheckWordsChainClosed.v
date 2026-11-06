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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/AnswerClosed.v, with its module names changed; 19 of its 42 lines of code are new or changed and 35 lines of the source are left out. *)
(* The closing pattern of the re-fit to statement passes 4-5 for check_words_chain: its ASan walk
   (lib/A/Prog/check_words_chain.v, tcheck_words_chain_ok) with the walk hypotheses (cgif's names)
   discharged at the pinned image (lib/A/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs,
   and the sink head AE2k.tfib_sink_head), by the kit's closing helpers (lib/A/Prog/CmdRecRest.v, CmdRecImg.v):
   TL is cmd_palib, TLF is cmd_palibf, IMG is cmd_img_facts_tfib, and the statement's side-stack laws are the
   kit's at tfibsegs: SMP is cmd_stack_malloc_progress, ASF cmd_astack_free_law, FFL cmd_frame_flag_law. The walk
   derives LAWS (YG0q.AR_laws_ok) and ML (from the entry's AR) itself and takes no PRW, SIGP or meter law. What
   remains is HB and the runtime entries' contracts at every FP state. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtShadow RtString RtNumber RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require check_words_chain_c check_words_chain.
Import ListNotations.
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PB_cmd s).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record *)
Hypothesis HB : CmdBSyms B.
Theorem tcheck_words_chain_closed
  (ASMALLOC4 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 4)
  (ASET00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_00) 0)
  (ASETF5 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f5) 0xf5)
  (ASETF8 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f8) 0xf8)
  (AATOI : forall fx0 : YK11.FPState,
     @aatoi_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8)
  (ASNPRINTF : forall fx0 : YK11.FPState,
     @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8)
  (ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp)) :
  @check_words_chain_c.tcheck_words_chain_spec fx rc AE2k.tfib_sink_head PB_cmd B MT.
Proof.
exact (@check_words_chain.tcheck_words_chain_ok fx rc AE2k.tfib_sink_head PB_cmd B MT
  ASMALLOC4 (CmdRecRest.cmd_stack_malloc_progress B) (CmdRecRest.cmd_astack_free_law B)
  (CmdRecRest.cmd_frame_flag_law B) ASET00 ASETF5 ASETF8 AATOI ASNPRINTF ASTRCMP HB
  (CmdRecRest.cmd_palib B HB) (CmdRecRest.cmd_palibf B HB) (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.
End closed.
