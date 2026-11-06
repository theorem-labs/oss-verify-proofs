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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/AnswerClosed.v, with its module names changed; 31 of its 58 lines of code are new or changed and 31 lines of the source are left out. *)
(* The closing pattern of the re-fit to statement passes 4-5 for check_words' ASan walk (lib/A/Prog/check_words.v,
   tcheck_words_ok): the per-binary walk facts it names are discharged at the pinned image (lib/A/Prog/CmdImg.v's
   instance PB_cmd, whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head) by the kit's closing lemmas,
   as A/Prog/SupRemoveAllRefitClosed.v does: LAWS is the core's AR_laws_ok, TL is cmd_palib, TLF is cmd_palibf, ML is
   cmd_model_laws, SIGP is cmd_sig_prog_PB, IMG is cmd_img_facts_tfib, and the side-stack laws SMP, ASF and FFL are
   cmd_stack_malloc_progress, cmd_astack_free_law and cmd_frame_flag_law. What remains is HB, the meter laws MTL and
   MTFL, and the callees' and runtime entries' contracts at every FP state. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m AB1v AB13.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaLibF CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtNumber RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require check_words.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.


Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PB_cmd s).
Variable B : asyms.
Variable MT : ameter_ops.
(* the allocator record and the meter's laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Theorem tcheck_words_closed
  (HJOINED : forall fx0 : YK11.FPState, @joined_c.tjoined_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (HADD : forall fx0 : YK11.FPState, @check_words_add_c.tcheck_words_add_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (HCHAIN : forall fx0 : YK11.FPState,
     @check_words_chain_c.tcheck_words_chain_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (HPIN : forall fx0 : YK11.FPState, @check_words_pin_set_c.tcwps_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc AE2k.tfib_sink_head SEGS B MT)
  (ASMALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0)
  (ASTRSPN : forall fx0 : YK11.FPState,
     @astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8)
  (ASTRCSPN : forall fx0 : YK11.FPState,
     @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8)
  (ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp))
  (AATOI : forall fx0 : YK11.FPState,
     @aatoi_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8)
  (ASNPRINTF : forall fx0 : YK11.FPState,
     @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8) :
  check_words_c.tcheck_words_spec B MT.
Proof.
exact (check_words.tcheck_words_ok B MT HJOINED HADD HCHAIN HPIN AFREE4 ASMALLOC0
  (CmdRecRest.cmd_stack_malloc_progress B) (CmdRecRest.cmd_astack_free_law B) (CmdRecRest.cmd_frame_flag_law B)
  ASTRSPN ASTRCSPN ASTRCMP AATOI ASNPRINTF HB (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palib B HB)
  (CmdRecRest.cmd_palibf B HB) (CmdRecRest.cmd_model_laws B HB) MTL MTFL (CmdRecImg.cmd_img_facts_tfib B HB)
  CmdRecRest.cmd_sig_prog_PB).
Qed.
End closed.
