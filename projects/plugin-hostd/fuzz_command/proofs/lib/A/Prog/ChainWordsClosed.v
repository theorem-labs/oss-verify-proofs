(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closing file of the ASan+UBSan walk of arg_line (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan), the pattern of a Theorem Labs lane's PASS4-REFIT.md section F (lib/A/Prog/SupRemoveAllRefitClosed.v,
   a working branch e84227c9553; a Theorem Labs lane's lib/A/Prog/RecBClosed.v, a working branch f349bdaedba): the
   walk's targ_line_holds (lib/B/Prog/arg_line.v) with the per-binary facts it names as Section hypotheses discharged
   at the pinned image (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink head
   YE2k.tfib_sink_head): cmd_val_objs_PB, cmd_sig_prog_PB and PRW (cmd_prw_tfib: the program's statics lie in
   tfibsegs' read-write window) are CmdRecRest's lemmas, cmd_img_facts_tfib is CmdRecImg's. What remains is the
   statement's own hypotheses (rec_canonical's contract and the strlen wrapper's, each at every FP state), HB and
   MTL. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/ArgLineClosed.v, with its module paths and module names changed; 21 of its 47 lines of code are new or changed and 20 lines of the source are left out. *)
(* The closing pattern of the re-fit to statement passes 4-5 for chain_words' ASan walk (lib/A/Prog/chain_words.v,
   chain_words_proved): the per-binary record hypotheses it names discharged at the pinned image (lib/A/Prog/CmdImg.v's
   instance PB_cmd, whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head), by the kit's closing
   helpers (lib/A/Prog/CmdRecRest.v), as SupRemoveAllRefitClosed.v does for the
   worked example: TL is cmd_palib, TLF is cmd_palibf, ML is cmd_model_laws, SIGP is cmd_sig_prog_PB, IMG is
   cmd_img_facts_tfib (the walk takes LAWS from the core's AR_laws_ok itself). What remains is the statement's own
   hypotheses (the callees' contracts and the runtime entries at every FP state, the side-stack laws SMP, ASF, FFL),
   HB, and the meter's laws MTL and MTFL. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require number_c sup_chain_c sup_resp_c chain_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require chain_words.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTFL : YC5d.ameter_fs_laws MT.
Theorem tchain_words_closed
  (NUMBER : forall fx0 : YK11.FPState, @number_c.tnumber_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (SUP_CHAIN : forall fx0 : YK11.FPState, @sup_chain_c.tsup_chain_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (SUP_RESP : forall fx0 : YK11.FPState, @sup_resp_c.tsup_resp_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (SM3 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 3)
  (SMP : stack_malloc_progressP B)
  (ASF : astack_free_law SEGS B)
  (FFL : frame_flag_lawP SEGS B)
  (SHF5 : forall fx0 : YK11.FPState,
     @RtShadow.aset_shadow_realizes fx0 rc SEGS B (@pa_sigma _ cmd_listing PB_cmd CS___asan_set_shadow_f5) 0xf5) :
  chain_words_c.tchain_words_spec B MT.
Proof.
exact (chain_words.chain_words_proved B MT NUMBER SUP_CHAIN SUP_RESP SM3 SMP ASF FFL SHF5 HB
  (CmdRecRest.cmd_palib B HB) (CmdRecRest.cmd_palibf B HB) (CmdRecRest.cmd_model_laws B HB) MTL MTFL
  CmdRecRest.cmd_sig_prog_PB (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.
End closed.
Print Assumptions tchain_words_closed.
