(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the closing step of the re-fit to statement passes 4-5 for check_refusal's ASan
   walk (lib/A/Prog/check_refusal.v, tcheck_refusal_spec_holds), as lib/A/Prog/SupRemoveAllRefitClosed.v does for
   sup_remove_all: the per-binary record hypotheses the walk names are discharged at the pinned image (CmdImg.v's
   instance PB_cmd, segments tfibsegs, sink head AE2k.tfib_sink_head): LAWS is the core's AR_laws_ok, TL is
   cmd_palib, SIGP is cmd_sig_prog_PB, IMG is cmd_img_facts_tfib. What remains is the statement's own hypothesis
   (sup_reply_code's contract at every FP state) and HB. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/CheckRefusalClosed.v, with its module paths and module names changed; 13 of its 34 lines of code are new or changed and 21 lines of the source are left out. *)
(* The closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F for check_words_pin_set's ASan+UBSan walk
   (lib/B/Prog/check_words_pin_set.v, pb_check_words_pin_set), the B twin of lib/A/Prog/CheckWordsAddClosed.v and
   lib/A/Prog/SupRemoveAllRefitClosed.v: the per-binary hypothesis the walk names besides HB is discharged at the
   pinned image (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink head
   YE2k.tfib_sink_head). TL is cmd_palib (lib/B/Prog/CmdRecRest.v). The walk takes no LAWS (it uses the core's
   AR_laws_ok itself), no SIGP, IMG or PRW, and no MTL: it allocates nothing and its post has no meter conjunct.
   What remains is the statement's own hypotheses (the strcmp and strncmp wrappers' contracts at every FP state)
   and HB. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require check_words_pin_set_c check_words_pin_set.
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
Theorem tcwps_closed
  (ASTRCMP : forall fx0 : YK11.FPState,
     @astrcmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcmp))
  (ASTRNCMP : forall fx0 : YK11.FPState,
     @astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp)) :
  check_words_pin_set_c.tcwps_spec B MT.
Proof.
exact (check_words_pin_set.pb_check_words_pin_set B MT (CmdRecRest.cmd_palib B HB) ASTRCMP ASTRNCMP HB).
Qed.
End closed.
