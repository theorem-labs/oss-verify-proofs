(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closing file of pins_clear's ASan+UBSan walk (a Theorem Labs lane's PASS4-REFIT.md
   section F): tpins_clear_closed proves the same tpins_clear_spec B MT as the walk's tpins_clear_holds
   (lib/B/Prog/pins_clear.v), at the pinned image (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are B's
   tfibsegs, and the sink head YE2k.tfib_sink_head), with the per-binary hypotheses the walk names discharged by
   exact, as a Theorem Labs lane's RecBClosed.v (a working branch f349bdaedba lib/A/Prog/RecBClosed.v:163-191)
   and SupRemoveAllRefitClosed.v (a working branch e84227c9553 lib/A/Prog/SupRemoveAllRefitClosed.v:50-60) do on
   image A: cmd_img_facts_tfib is CmdRecImg.cmd_img_facts_tfib, cmd_sig_prog_PB and VOBJS are CmdRecRest's
   cmd_sig_prog_PB and cmd_val_objs_PB, and PRW is CmdRecRest's cmd_prw_tfib (the program's statics lie in B's
   read-write window, lib/B/YB13.v's tfib_rw_window). What remains is the callees' contracts at every FP state (the
   statement's TRECORD, TARG_S, TMIX_CALL, TANSWER_CODE), HB and MTL. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require record_c arg_s_c mix_call_c answer_code_c pins_clear_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require pins_clear.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Theorem tpins_clear_closed
  (TRECORD : forall fx0 : YK11.FPState, @record_c.trecord_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TARG_S : forall fx0 : YK11.FPState, @arg_s_c.targ_s_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TMIX_CALL : forall fx0 : YK11.FPState, @mix_call_c.tmix_call_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TANSWER_CODE : forall fx0 : YK11.FPState,
     @answer_code_c.tanswer_code_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT) :
  @pins_clear_c.tpins_clear_spec fx rc YE2k.tfib_sink_head PB_cmd B MT.
Proof.
exact (@pins_clear.tpins_clear_holds fx rc YE2k.tfib_sink_head PB_cmd B MT TRECORD TARG_S TMIX_CALL TANSWER_CODE
  CmdRecRest.cmd_val_objs_PB HB MTL CmdRecRest.cmd_sig_prog_PB CmdRecImg.cmd_img_facts_tfib (CmdRecRest.cmd_prw_tfib B HB)).
Qed.
End closed.
Print Assumptions tpins_clear_closed.
About tpins_clear_closed.
