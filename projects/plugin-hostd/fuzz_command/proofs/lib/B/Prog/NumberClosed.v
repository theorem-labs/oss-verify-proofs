(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the closing step of the re-fit to statement passes 4-5 for check_refusal's ASan
   walk (lib/A/Prog/check_refusal.v, tcheck_refusal_spec_holds), as lib/A/Prog/SupRemoveAllRefitClosed.v does for
   sup_remove_all: the per-binary record hypotheses the walk names are discharged at the pinned image (CmdImg.v's
   instance PB_cmd, segments tfibsegs, sink head AE2k.tfib_sink_head): LAWS is the core's AR_laws_ok, TL is
   cmd_palib, SIGP is cmd_sig_prog_PB, IMG is cmd_img_facts_tfib. What remains is the statement's own hypothesis
   (sup_reply_code's contract at every FP state) and HB. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/CheckRefusalClosed.v, with its module paths and module names changed; 13 of its 39 lines of code are new or changed and 16 lines of the source are left out. *)
(* The closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F for number's ASan+UBSan walk (lib/B/Prog/numberA.v with
   numberE / numberK / numberR / numberB, number_walk), the B twin of lib/A/Prog/NumberClosed.v (a Theorem Labs lane's A
   re-fit of number): the per-binary record hypotheses the walk names besides HB are discharged at the pinned image
   (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink head YE2k.tfib_sink_head): TL
   is CmdRecRest.cmd_palib, TLF is CmdRecRest.cmd_palibf, IMG is CmdRecImg.cmd_img_facts_tfib, and the side-stack
   laws SMP, ASF and FFL are CmdRecRest's cmd_stack_malloc_progress, cmd_astack_free_law and cmd_frame_flag_law. The
   walk takes LAWS and ML as base lemmas already. What remains is the statement's own runtime hypotheses (SM0 and
   STRTOL at every FP state) and HB. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtNumber.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdImg CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require number_c numberA.
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
(* the allocator record (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Theorem tnumber_closed
  (SM0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0)
  (STRTOL : forall fx0 : YK11.FPState,
     @RtNumber.astrtol_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strtol) 0xa6bf8 0x604158) :
  number_c.tnumber_spec B MT.
Proof.
exact (numberA.number_walk B MT SM0 (CmdRecRest.cmd_stack_malloc_progress B) (CmdRecRest.cmd_astack_free_law B)
  (CmdRecRest.cmd_frame_flag_law B) STRTOL HB (CmdRecRest.cmd_palib B HB) (CmdRecRest.cmd_palibf B HB)
  (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.
End closed.
Print Assumptions tnumber_closed.
