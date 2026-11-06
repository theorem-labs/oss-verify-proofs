(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closing pattern of the statement-pass re-fit for verbs_receive's ASan
   walk (lib/A/Prog/verbs_receive_top.v, tverbs_receive) at the pinned image (lib/A/Prog/CmdImg.v's instance PB_cmd,
   whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head), as SupRemoveAllRefitClosed.v does. The
   record hypotheses come from the A kit (CmdRecImg.v, CmdRecRest.v): IMG is cmd_img_facts_tfib, TL is cmd_palib,
   TLF is cmd_palibf, ML is cmd_model_laws, SIGP is cmd_sig_prog_PB, VOBJS / VHIS are cmd_val_objs_PB /
   cmd_val_his_PB, PRW is cmd_prw_tfib, SMP is cmd_stack_malloc_progress, ASF is cmd_astack_free_law and FFL is
   cmd_frame_flag_law (LAWS is the core's AR_laws_ok, inside verbs_receive_top.v). What remains is the statement's own
   hypotheses (the callees' contracts and the runtime entries), HB, MTL and MTFL. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/VerbsReceiveClosed.v, with its module paths and module names changed; 27 of its 55 lines of code are new or changed and 90 lines of the source are left out. *)
(* The closing pattern of the re-fit to statement passes 4-5 for check_words' ASan+UBSan walk (lib/B/Prog/check_words.v,
   tcheck_words_proof): the per-binary record hypotheses the walk names besides HB are discharged at the pinned image
   (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink head YE2k.tfib_sink_head) by the
   B kit's closers in lib/B/Prog/CmdRecRest.v: TL by cmd_palib, TLF by cmd_palibf (from
   cmd_uar_cells), SIGP by cmd_sig_prog_PB, and the statement's side-stack laws SMP, ASF, FFL by
   cmd_stack_malloc_progress, cmd_astack_free_law, cmd_frame_flag_law; IMG by CmdRecImg.cmd_img_facts_tfib. The walk
   takes LAWS and ML as base lemmas already. What remains is the statement's callee contracts and runtime entries (at
   every FP state), HB, and the meter laws MTL and MTFL. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtString RtNumber RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdImg CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib CmdRecBase CmdBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg CmdRecRest PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require check_words_c check_words.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PB_cmd).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTFL : YC5d.ameter_fs_laws MT.
Theorem tcheck_words_closed
  (HJOINED : forall fx0 : YK11.FPState, @tjoined_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (HADD : forall fx0 : YK11.FPState, @tcheck_words_add_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (HCHAIN : forall fx0 : YK11.FPState, @tcheck_words_chain_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (HPIN : forall fx0 : YK11.FPState, @tcwps_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc YE2k.tfib_sink_head SEGS B MT)
  (ASMALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0)
  (ASTRSPN : forall fx0 : YK11.FPState, @astrspn_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strspn) 0xa6bf8 0x604158)
  (ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158)
  (ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcmp))
  (AATOI : forall fx0 : YK11.FPState, @aatoi_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158)
  (ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158) :
  check_words_c.tcheck_words_spec B MT.
Proof.
pose proof (CmdRecRest.cmd_palib B HB) as TL.
pose proof (CmdRecRest.cmd_palibf (rc := rc) B HB) as TLF.
pose proof (CmdRecImg.cmd_img_facts_tfib B HB) as IMG.
pose proof (CmdRecRest.cmd_stack_malloc_progress B) as SMP.
pose proof (CmdRecRest.cmd_astack_free_law B) as ASF.
pose proof (CmdRecRest.cmd_frame_flag_law B) as FFL.
apply (check_words.tcheck_words_proof B MT); first [assumption | exact CmdRecRest.cmd_sig_prog_PB].
Qed.
End closed.
