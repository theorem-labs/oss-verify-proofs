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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/VerbsReceiveClosed.v, with its module paths and module names changed; 16 of its 45 lines of code are new or changed and 89 lines of the source are left out. *)
(* The closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F for pin_set_words' ASan+UBSan walk
   (lib/B/Prog/pin_set_words.v, tpin_set_words_proof): the per-binary record hypotheses it names discharged at the
   pinned B image (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink head
   YE2k.tfib_sink_head), as A's ReplyClosed.v (a working branch d9dcf6ff848) does: TL is cmd_palib, SIGP is
   cmd_sig_prog_PB, IMG is cmd_img_facts_tfib (the walk takes LAWS as the core's AR_laws_ok itself and names no PRW).
   What remains is the statement's own hypotheses (pins_set's and lv2_refusals_forget's contracts and the strlen and
   strncmp wrappers' contracts, at every FP state), HB and MTL. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require pins_set_c lv2_refusals_forget_c pin_set_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require pin_set_words.
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
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Theorem tpin_set_words_closed
  (PINS_SET : forall fx0 : YK11.FPState,
     @pins_set_c.tpins_set_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (LV2_REFUSALS_FORGET : forall fx0 : YK11.FPState,
     @lv2_refusals_forget_c.tlv2_refusals_forget_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (STRLEN : forall fx0 : YK11.FPState,
     @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strlen))
  (STRNCMP : forall fx0 : YK11.FPState,
     @RtString.astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp)) :
  pin_set_words_c.tpin_set_words_spec B MT.
Proof.
exact (pin_set_words.tpin_set_words_proof B MT PINS_SET LV2_REFUSALS_FORGET STRLEN STRNCMP
  (CmdRecRest.cmd_palib B HB) HB (CmdRecImg.cmd_img_facts_tfib B HB) MTL CmdRecRest.cmd_sig_prog_PB).
Qed.
End closed.
Print Assumptions tpin_set_words_closed.
