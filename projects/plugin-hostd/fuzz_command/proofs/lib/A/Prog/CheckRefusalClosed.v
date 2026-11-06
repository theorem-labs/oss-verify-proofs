(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the closing step of the re-fit to statement passes 4-5 for check_refusal's ASan
   walk (lib/A/Prog/check_refusal.v, tcheck_refusal_spec_holds), as lib/A/Prog/SupRemoveAllRefitClosed.v does for
   sup_remove_all: the per-binary record hypotheses the walk names are discharged at the pinned image (CmdImg.v's
   instance PB_cmd, segments tfibsegs, sink head AE2k.tfib_sink_head): LAWS is the core's AR_laws_ok, TL is
   cmd_palib, SIGP is cmd_sig_prog_PB, IMG is cmd_img_facts_tfib. What remains is the statement's own hypothesis
   (sup_reply_code's contract at every FP state) and HB. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require sup_reply_code_c check_refusal_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require check_refusal.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record *)
Hypothesis HB : CmdBSyms B.
Theorem tcheck_refusal_closed
  (HSUP_REPLY_CODE : forall fx0 : YK11.FPState,
     @sup_reply_code_c.tsup_reply_code_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT) :
  check_refusal_c.tcheck_refusal_spec B MT.
Proof.
exact (check_refusal.tcheck_refusal_spec_holds B MT HSUP_REPLY_CODE HB
  (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palib B HB) CmdRecRest.cmd_sig_prog_PB
  (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.
End closed.
Print Assumptions tcheck_refusal_closed.
