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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/PinsClearClosed.v, with its module names changed; 15 of its 44 lines of code are new or changed and 20 lines of the source are left out. *)
(* sup_remove's ASan+UBSan walk closed at the pinned B image (the common closing pattern, the B twin of
   lib/A/Prog/SupRemoveAllRefitClosed.v): tsup_remove_closed proves tsup_remove_spec B MT at the instance PB_cmd
   (lib/B/Prog/CmdImg.v, segments tfibsegs) and the sink head YE2k.tfib_sink_head, from the statement's callee and
   runtime contracts (forall fx0), HB, MTL and MTFL only. The walk hypotheses are discharged here by the kit:
   LAWS is the core's AR_laws_ok, TL is cmd_palib, TLF is cmd_palibf, FFL is cmd_frame_flag_law, SIGP is
   cmd_sig_prog_PB, IMG is cmd_img_facts_tfib, VOBJS is cmd_val_objs_PB (all lib/B/Prog/CmdRecRest.v and
   CmdRecImg.v). sup_remove.v's theorem already closes ML (from AR's universe at the entry), SMP and ASF. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRest PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require record_c arg_s_c answer_c sup_remove_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require sup_remove.
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
(* the allocator record and the meter's laws, with the frame laws for the side-stack frame's take and release
   (the walk hypotheses HB, MTL, MTFL) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTFL : YC5d.ameter_fs_laws MT.
Theorem tsup_remove_closed
  (TRECORD : forall fx0 : YK11.FPState, @record_c.trecord_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TARG_S : forall fx0 : YK11.FPState, @arg_s_c.targ_s_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0)
  (ASNPRINTF : forall fx0 : YK11.FPState,
     @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158) :
  sup_remove_c.tsup_remove_spec B MT.
Proof.
exact (sup_remove.tsup_remove_spec_holds B MT TRECORD TARG_S TANSWER ASTACK_MALLOC0 ASNPRINTF
  CmdRecRest.cmd_val_objs_PB HB (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palib B HB) (CmdRecRest.cmd_palibf B HB)
  MTL MTFL (CmdRecRest.cmd_frame_flag_law B) (CmdRecImg.cmd_img_facts_tfib B HB) CmdRecRest.cmd_sig_prog_PB).
Qed.
End closed.
