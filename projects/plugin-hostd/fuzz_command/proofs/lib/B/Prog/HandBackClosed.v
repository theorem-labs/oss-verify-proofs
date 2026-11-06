(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F for hand_back's ASan+UBSan
   walk (lib/B/Prog/hand_back.v, thand_back_holds), as lib/A/Prog/SupRemoveAllRefitClosed.v (a working branch
   e84227c9553) and a Theorem Labs lane's RecBClosed.v (a working branch f349bdaedba) do on the A side: the
   per-binary hypotheses the walk names are discharged at the pinned image (lib/B/Prog/CmdImg.v's instance PB_cmd,
   whose segments are tfibsegs, and the sink head YE2k.tfib_sink_head): VOBJS, cmd_val_his_PB, cmd_sig_prog_PB and
   cmd_palib are a Theorem Labs lane's lemmas cmd_val_objs_PB, cmd_val_his_PB, cmd_sig_prog_PB and cmd_palib (lib/B/Prog/CmdRecRest.v),
   cmd_img_facts_tfib is CmdRecImg.v's, and PRW is CmdRecRest.v's cmd_prw_tfib (the program's statics lie in tfibsegs'
   read-write window). What remains is the statement's own contracts (the callee's and the runtime entries' at
   every FP state), HB and MTL. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require xmalloc_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require hand_back.
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
Theorem thand_back_closed
  (TXMALLOC : forall fx0 : YK11.FPState, @xmalloc_c.txmalloc_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (AFREE4 : forall fx0 : YK11.FPState, @YC5d.afree04_rule fx0 rc YE2k.tfib_sink_head SEGS B MT)
  (AFREE_NULL4 : forall fx0 : YK11.FPState, @YC5d.afree_null04_rule fx0 rc YE2k.tfib_sink_head SEGS B MT)
  (AMEMCPY : forall fx0 : YK11.FPState, @YG0d.aintrin_realizes fx0 rc SEGS B YG0d.OCpy (SIG CS___asan_memcpy))
  (ASTRLEN : forall fx0 : YK11.FPState,
     @RtString.astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen)) :
  hand_back_c.thand_back_spec B MT.
Proof.
exact (hand_back.thand_back_holds B MT TXMALLOC AFREE4 AFREE_NULL4 AMEMCPY ASTRLEN CmdRecRest.cmd_val_objs_PB HB MTL
  CmdRecRest.cmd_val_his_PB CmdRecRest.cmd_sig_prog_PB CmdRecImg.cmd_img_facts_tfib CmdRecRest.cmd_palib
  (CmdRecRest.cmd_prw_tfib B HB)).
Qed.
End closed.
Print Assumptions thand_back_closed.
About thand_back_closed.
