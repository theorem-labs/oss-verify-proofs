(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closing pattern of the statement-pass re-fit for verbs_receive's ASan
   walk (lib/A/Prog/verbs_receive_top.v, tverbs_receive) at the pinned image (lib/A/Prog/CmdImg.v's instance PB_cmd,
   whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head), as SupRemoveAllRefitClosed.v does. The
   record hypotheses come from the A kit (CmdRecImg.v, CmdRecRest.v): IMG is cmd_img_facts_tfib, TL is cmd_palib,
   TLF is cmd_palibf, ML is cmd_model_laws, SIGP is cmd_sig_prog_PB, VOBJS / VHIS are cmd_val_objs_PB /
   cmd_val_his_PB, PRW is cmd_prw_tfib, SMP is cmd_stack_malloc_progress, ASF is cmd_astack_free_law and FFL is
   cmd_frame_flag_law (LAWS is the core's AR_laws_ok, inside verbs_receive_top.v). What remains is the statement's own
   hypotheses (the callees' contracts and the runtime entries), HB, MTL and MTFL. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/VerbsReceiveClosed.v, with its module paths and module names changed; 14 of its 44 lines of code are new or changed and 88 lines of the source are left out. *)
(* The closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F for chain_words' ASan+UBSan walk (lib/B/Prog/
   chain_words.v, chain_words_proved): the per-binary record hypotheses it names discharged at the pinned image
   (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink head YE2k.tfib_sink_head),
   as A's worked example lib/A/Prog/SupRemoveAllRefitClosed.v does: LAWS is the core's AR_laws_ok (inside the
   walk), IMG is CmdRecImg.cmd_img_facts_tfib (lib/B/Prog/CmdRecImg.v:83), and the kit's lib/B/Prog/CmdRecRest.v
   gives the rest: SMP is cmd_stack_malloc_progress (:152), FFL is cmd_frame_flag_law (:154), ASF is
   cmd_astack_free_law (:167), ML is cmd_model_laws (:194), TLF is cmd_palibf (:197), TL is cmd_palib (:208),
   SIGP is cmd_sig_prog_PB (:256). What remains is the statement's own hypotheses (the callees' and runtime
   entries' contracts at every FP state), HB and the meter's laws MTL and MTFL. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require number_c sup_chain_c sup_resp_c chain_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require chain_words.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PB_cmd).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTFL : YC5d.ameter_fs_laws MT.
Theorem tchain_words_closed
  (NUMBER : forall fx0 : YK11.FPState, @number_c.tnumber_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (SUP_CHAIN : forall fx0 : YK11.FPState, @sup_chain_c.tsup_chain_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (SUP_RESP : forall fx0 : YK11.FPState, @sup_resp_c.tsup_resp_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (SM3 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 3)
  (SHF5 : forall fx0 : YK11.FPState,
     @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIGMA CS___asan_set_shadow_f5) 0xf5) :
  chain_words_c.tchain_words_spec B MT.
Proof.
exact (chain_words.chain_words_proved B MT NUMBER SUP_CHAIN SUP_RESP SM3 (CmdRecRest.cmd_stack_malloc_progress B)
  (CmdRecRest.cmd_astack_free_law B) (CmdRecRest.cmd_frame_flag_law B) SHF5 HB (CmdRecRest.cmd_palib B HB)
  (CmdRecRest.cmd_palibf B HB) (CmdRecRest.cmd_model_laws B HB) MTL MTFL CmdRecRest.cmd_sig_prog_PB
  (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.
End closed.
