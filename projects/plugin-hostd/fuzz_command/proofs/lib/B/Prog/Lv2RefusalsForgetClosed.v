(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the closing corollary of lv2_refusals_forget's ASan+UBSan walk
   (lib/B/Prog/lv2_refusals_forget.v, tlv2_refusals_forget_holds), in the pattern of a Theorem Labs lane's PASS4-REFIT.md section F
   (lib/A/Prog/SupRemoveAllRefitClosed.v; a Theorem Labs lane's RecBClosed.v): the walk's per-binary hypotheses are
   discharged at the pinned image B (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink
   head YE2k.tfib_sink_head): VOBJS, cmd_sig_prog_PB, cmd_val_his_PB and PRW by a Theorem Labs lane's lemmas cmd_val_objs_PB,
   cmd_sig_prog_PB, cmd_val_his_PB and cmd_prw_tfib (lib/B/Prog/CmdRecRest.v), cmd_img_facts_tfib by a Theorem Labs lane's lemma of
   that name (lib/B/Prog/CmdRecImg.v). What remains is the statement's callee contracts (at every FP state), HB and
   MTL. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require record_c arg_s_c mix_call_c lv2_refusals_forget_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require lv2_refusals_forget.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Theorem tlv2_refusals_forget_closed
  (TRECORD : forall fx0 : YK11.FPState, @record_c.trecord_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TARG_S : forall fx0 : YK11.FPState, @arg_s_c.targ_s_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TMIX_CALL : forall fx0 : YK11.FPState, @mix_call_c.tmix_call_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT) :
  lv2_refusals_forget_c.tlv2_refusals_forget_spec B MT.
Proof.
exact (lv2_refusals_forget.tlv2_refusals_forget_holds B MT TRECORD TARG_S TMIX_CALL CmdRecRest.cmd_val_objs_PB HB MTL
  CmdRecRest.cmd_sig_prog_PB CmdRecRest.cmd_val_his_PB CmdRecImg.cmd_img_facts_tfib (CmdRecRest.cmd_prw_tfib B HB)).
Qed.
End closed.
