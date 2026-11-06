(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the closing step of the re-fit to statement passes 4-5 for check_refusal's ASan
   walk (lib/A/Prog/check_refusal.v, tcheck_refusal_spec_holds), as lib/A/Prog/SupRemoveAllRefitClosed.v does for
   sup_remove_all: the per-binary record hypotheses the walk names are discharged at the pinned image (CmdImg.v's
   instance PB_cmd, segments tfibsegs, sink head AE2k.tfib_sink_head): LAWS is the core's AR_laws_ok, TL is
   cmd_palib, SIGP is cmd_sig_prog_PB, IMG is cmd_img_facts_tfib. What remains is the statement's own hypothesis
   (sup_reply_code's contract at every FP state) and HB. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/CheckRefusalClosed.v, with its module paths and module names changed; 15 of its 36 lines of code are new or changed and 21 lines of the source are left out. *)
(* The closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F for is_instance_verb's ASan+UBSan walk
   (lib/B/Prog/is_instance_verb.v + is_instance_verb_s1.v, is_instance_verb_ok), the B twin of
   lib/A/Prog/IsInstanceVerbClosed.v (a working branch 44a0ed8b759): the per-binary record
   hypotheses the walk names besides HB are discharged at the pinned image (lib/B/Prog/CmdImg.v's instance PB_cmd,
   whose segments are tfibsegs, and the sink head YE2k.tfib_sink_head): TL is CmdRecRest.cmd_palib
   (lib/B/Prog/CmdRecRest.v:138) and IMG is CmdRecImg.cmd_img_facts_tfib (lib/B/Prog/CmdRecImg.v:83). The walk takes
   LAWS as the core's AR_laws_ok itself and names no SIGP, PRW or MTL (it allocates nothing and its post has no meter
   conjunct). What remains is the statement's own runtime hypotheses (the strcspn and strncmp wrappers' contracts at
   every FP state) and HB. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require is_instance_verb_c is_instance_verb.
Import ListNotations.
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
Theorem tis_instance_verb_closed
  (STRCSPN : forall fx0 : YK11.FPState,
     @RtString.astrcspn_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158)
  (STRNCMP : forall fx0 : YK11.FPState,
     @RtString.astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp)) :
  is_instance_verb_c.tis_instance_verb_spec B MT.
Proof.
exact (is_instance_verb.is_instance_verb_ok B MT HB (CmdRecRest.cmd_palib B HB) (CmdRecImg.cmd_img_facts_tfib B HB)
  STRCSPN STRNCMP).
Qed.
End closed.
Print Assumptions tis_instance_verb_closed.
