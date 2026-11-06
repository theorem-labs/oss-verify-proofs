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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/HandBackClosed.v, with its module names changed; 18 of its 42 lines of code are new or changed and 29 lines of the source are left out. *)
(* The closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F for answer_code's ASan+UBSan walk (lib/B/Prog/answer_code.v,
   tanswer_code_holds): the per-binary facts the walk names as Section hypotheses are discharged at the pinned image
   (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are B's tfibsegs, and B's sink head YE2k.tfib_sink_head), as
   a Theorem Labs lane's RecBClosed.v (a working branch f349bdaedba, lib/A/Prog/RecBClosed.v:163-191) and
   a Theorem Labs lane's SupRemoveAllRefitClosed.v (a working branch e84227c9553) do on the ASan side: LAWS is the core's AR_laws_ok
   (inside the walk), IMG is cmd_img_facts_tfib, the walk's cmd_palib / cmd_sig_prog_PB are a Theorem Labs lane's lemmas of those
   names, the statement's VOBJS is cmd_val_objs_PB, TLF (PaLibF.PALibF) is cmd_palibf (from HB's constant cells), the
   walk's cmd_frame_flag_law is a Theorem Labs lane's lemma of that name, and the statement's AFREE_LAW (the side-stack release law
   astack_free_law, YG0d.v:309; not free()'s contract, which is AFREE4) is cmd_astack_free_law (all CmdRecRest.v).
   What remains is the statement's callee and runtime contracts (at every FP state) other than AFREE_LAW, HB, MTL and
   MTLF. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRest PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require hand_back_c answer_code_c answer_code.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1; MTLF: cgif's MLAWF) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTLF : YC5d.ameter_fs_laws MT.
Theorem tanswer_code_closed
  (THAND_BACK : forall fx0 : YK11.FPState, @hand_back_c.thand_back_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (AFREE4 : forall fx0 : YK11.FPState, @YC5d.afree04_rule fx0 rc YE2k.tfib_sink_head SEGS B MT)
  (ASTACK1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1)
  (ASNPRINTF : forall fx0 : YK11.FPState,
     @RtFormat.asnprintf_realizes fx0 rc SEGS B (@pa_sigma _ cmd_listing PB_cmd CS___interceptor_trampoline_snprintf)
       0xa6bf8 0x604158) :
  @answer_code_c.tanswer_code_spec fx rc YE2k.tfib_sink_head PB_cmd B MT.
Proof.
exact (@answer_code.tanswer_code_holds fx rc YE2k.tfib_sink_head PB_cmd B MT THAND_BACK AFREE4 ASTACK1
  (CmdRecRest.cmd_astack_free_law B) ASNPRINTF (@CmdRecRest.cmd_val_objs_PB rc) HB (CmdRecRest.cmd_palibf B HB)
  MTL MTLF (@CmdRecRest.cmd_palib rc) (@CmdRecRest.cmd_sig_prog_PB rc) CmdRecImg.cmd_img_facts_tfib
  CmdRecRest.cmd_frame_flag_law).
Qed.
End closed.
Print Assumptions tanswer_code_closed.
