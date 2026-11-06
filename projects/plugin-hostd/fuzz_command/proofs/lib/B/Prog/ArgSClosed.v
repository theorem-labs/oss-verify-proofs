(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F for arg_s's ASan+UBSan
   walk (lib/B/Prog/arg_s.v, targ_s_holds), as lib/B/Prog/HandBackClosed.v (a working branch 30b80f50c51)
   does for hand_back: the per-binary hypotheses the walk names are discharged at the pinned image (lib/B/Prog/CmdImg.v's
   instance PB_cmd, whose segments are tfibsegs, and the sink head YE2k.tfib_sink_head): VOBJS, cmd_sig_prog_PB and
   PRW are a Theorem Labs lane's lemmas cmd_val_objs_PB, cmd_sig_prog_PB and cmd_prw_tfib (lib/B/Prog/CmdRecRest.v), and
   cmd_img_facts_tfib is CmdRecImg.v's. What remains is the statement's own contracts (the callee's and the runtime
   entries' at every FP state), HB and MTL. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require xmalloc_c arg_s_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require arg_s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PB_cmd c).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Theorem targ_s_closed
  (TXMALLOC : forall fx0 : YK11.FPState, @xmalloc_c.txmalloc_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (AMEMCPY : forall fx0 : YK11.FPState, @YG0d.aintrin_realizes fx0 rc SEGS B YG0d.OCpy (SIG CS___asan_memcpy))
  (ASTRLEN : forall fx0 : YK11.FPState,
     @RtString.astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen)) :
  arg_s_c.targ_s_spec B MT.
Proof.
exact (arg_s.targ_s_holds B MT TXMALLOC AMEMCPY ASTRLEN CmdRecRest.cmd_val_objs_PB HB MTL
  CmdRecRest.cmd_sig_prog_PB CmdRecImg.cmd_img_facts_tfib (CmdRecRest.cmd_prw_tfib B HB)).
Qed.
End closed.
Print Assumptions targ_s_closed.
About targ_s_closed.
