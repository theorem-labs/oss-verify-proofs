(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the closing file of the B walk of sup_chain_clear on plugin-hostd/
   fuzz_command's ASan+UBSan image (lib/B/Prog/sup_chain_clear.v), as a Theorem Labs lane's PASS4-REFIT.md section F asks: the
   per-binary record hypotheses the walk names are discharged at the pinned image (lib/B/Prog/CmdImg.v's PB_cmd,
   whose segments are tfibsegs and whose sink head is YE2k.tfib_sink_head), as a Theorem Labs lane's lib/A/Prog/
   RecBClosed.v and a Theorem Labs lane's lib/A/Prog/SupRemoveAllRefitClosed.v do: VOBJS is CmdRecRest.cmd_val_objs_PB, TL is
   cmd_palib, TLF is cmd_palibf, SIGP is cmd_sig_prog_PB, IMG is CmdRecImg.cmd_img_facts_tfib and the side-stack
   free law is cmd_astack_free_law (the walk needs no PRW: it writes the program's statics only through its callees). What remains is HB, the meter's laws and the callees' and the
   runtime's contracts at every FP state. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib CmdRecFacts PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require record_c arg_s_c rec_shape_of_c answer_c sup_chain_clear_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require sup_chain_clear.
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
Hypothesis MTLF : YC5d.ameter_fs_laws MT.
Theorem tsup_chain_clear_closed
  (TRECORD : forall fx0 : YK11.FPState, @record_c.trecord_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TARG_S : forall fx0 : YK11.FPState, @arg_s_c.targ_s_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TREC_SHAPE_OF : forall fx0 : YK11.FPState, @rec_shape_of_c.trec_shape_of_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TANSWER : forall fx0 : YK11.FPState, @answer_c.tanswer_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0)
  (ASNPRINTF : forall fx0 : YK11.FPState,
     @RtFormat.asnprintf_realizes fx0 rc SEGS B (@pa_sigma _ cmd_listing PB_cmd CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158) :
  sup_chain_clear_c.tsup_chain_clear_spec B MT.
Proof.
exact (sup_chain_clear.tsup_chain_clear_holds B MT TRECORD TARG_S TREC_SHAPE_OF TANSWER ASTACK_MALLOC0
  (CmdRecRest.cmd_astack_free_law B) ASNPRINTF CmdRecRest.cmd_val_objs_PB HB (CmdRecRest.cmd_palib B HB)
  (CmdRecRest.cmd_palibf B HB) MTL MTLF CmdRecRest.cmd_sig_prog_PB CmdRecImg.cmd_img_facts_tfib).
Qed.
End closed.
About tsup_chain_clear_closed.
Print Assumptions tsup_chain_clear_closed.
