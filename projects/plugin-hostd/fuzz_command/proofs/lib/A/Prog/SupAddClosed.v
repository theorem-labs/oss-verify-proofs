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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/HandBackClosed.v, with its module paths and module names changed; 31 of its 58 lines of code are new or changed and 26 lines of the source are left out. *)
(* The closing pattern of the statement-pass re-fit for sup_add's ASan walk (lib/A/Prog/sup_add.v,
   sup_add_holds): tsup_add_closed proves the same tsup_add_spec B MT at the pinned image (lib/A/Prog/CmdImg.v's
   instance PB_cmd, whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head), with the walk hypotheses
   (cgif's names) discharged there by the kit's closing helpers (lib/A/Prog/CmdRecRest.v) and the core: LAWS is
   the core's AR_laws_ok, TL is cmd_palib, TLF is cmd_palibf, ML is
   cmd_model_laws, SMP is cmd_stack_malloc_progress, ASF is cmd_astack_free_law, FFL is cmd_frame_flag_law, VHIS is
   cmd_val_his_PB, SIGP is cmd_sig_prog_PB, PRW is cmd_prw_tfib, IMG is cmd_img_facts_tfib and VOBJS is
   cmd_val_objs_PB. What remains: the statement's own hypotheses (the callees' and the runtime entries' contracts at
   every FP state), HB, MTL and MTFL (the meter's frame laws, for the side-stack frame). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d YG0q YG05 YG0t.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require
rec_calls_free_c xstrdup_c arg_i_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require sup_add.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PB_cmd c).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record, the meter's laws and its frame laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTFL : YC5d.ameter_fs_laws MT.
Theorem tsup_add_closed
  (TREC_CALLS_FREE : forall fx0 : YK11.FPState,
     @rec_calls_free_c.trec_calls_free_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (TXSTRDUP : forall fx0 : YK11.FPState, @xstrdup_c.txstrdup_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (TARG_I : forall fx0 : YK11.FPState, @arg_i_c.targ_i_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (TMIX_CALL : forall fx0 : YK11.FPState, @mix_call_c.tmix_call_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (THAND_BACK : forall fx0 : YK11.FPState, @hand_back_c.thand_back_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (ASTACK_MALLOC1 : forall fx0 : YK11.FPState, @YG0d.astack_malloc_realizes fx0 rc SEGS B 1)
  (ASNPRINTF : forall fx0 : YK11.FPState, @RtFormat.asnprintf_realizes fx0 rc SEGS B
     (SIG CmdSyms.CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8) :
  sup_add_c.tsup_add_spec B MT.
Proof.
pose proof (sup_add.sup_add_holds (fx := fx) B MT) as P.
repeat match type of P with
| ?A -> _ => lazymatch type of A with Prop =>
    specialize (P ltac:(first [ assumption
      | exact (YG0q.AR_laws_ok SEGS B) | exact (CmdRecRest.cmd_palib B HB) | exact (CmdRecRest.cmd_palibf B HB)
      | exact (CmdRecRest.cmd_model_laws B HB) | exact (CmdRecRest.cmd_stack_malloc_progress B)
      | exact (CmdRecRest.cmd_astack_free_law B) | exact (CmdRecRest.cmd_frame_flag_law B)
      | exact CmdRecRest.cmd_val_his_PB | exact CmdRecRest.cmd_sig_prog_PB | exact CmdRecRest.cmd_val_objs_PB
      | exact (CmdRecRest.cmd_prw_tfib B HB) | exact (CmdRecImg.cmd_img_facts_tfib B HB) ])) end
end.
exact P.
Qed.
End closed.
Print Assumptions tsup_add_closed.
