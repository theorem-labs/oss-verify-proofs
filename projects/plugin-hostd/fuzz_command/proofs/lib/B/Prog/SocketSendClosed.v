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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/VerbsReceiveClosed.v, with its module paths and module names changed; 14 of its 39 lines of code are new or changed and 93 lines of the source are left out. *)
(* The closing file of socket_send's ASan+UBSan walk (a Theorem Labs lane's PASS4-REFIT.md section F): `tsocket_send_closed` proves
   the same `tsocket_send_spec B MT` (lib/B/Prog/socket_send_c.v, a working branch fc8bcbd8b42) as the walk's
   tsocket_send_holds (lib/B/Prog/socket_send.v), at the pinned image (lib/B/Prog/CmdImg.v's instance PB_cmd, whose
   segments are B's tfibsegs, and the sink head YE2k.tfib_sink_head), with the per-binary facts the walk names as
   Section hypotheses discharged by a Theorem Labs lane's lemmas of the same names: cmd_val_objs_PB, cmd_palib, cmd_sig_prog_PB and
   cmd_prw_tfib (PRW: the program's statics lie in tfibsegs' read-write window) of lib/B/Prog/CmdRecRest.v, and
   cmd_img_facts_tfib of lib/B/Prog/CmdRecImg.v. What remains is the statement's own callee and runtime contracts (at
   every FP state), HB and MTL. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require xmalloc_c socket_send_c socket_send.
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
Theorem tsocket_send_closed
  (TXMALLOC : forall fx0 : YK11.FPState, @xmalloc_c.txmalloc_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (AFREE4 : forall fx0 : YK11.FPState, @YC5d.afree04_rule fx0 rc YE2k.tfib_sink_head SEGS B MT)
  (AFREE_NULL4 : forall fx0 : YK11.FPState, @YC5d.afree_null04_rule fx0 rc YE2k.tfib_sink_head SEGS B MT)
  (AMEMSET : forall fx0 : YK11.FPState, @YG0d.aintrin_realizes fx0 rc SEGS B YG0d.OSet (SIG CS___asan_memset))
  (AMEMCPY : forall fx0 : YK11.FPState, @YG0d.aintrin_realizes fx0 rc SEGS B YG0d.OCpy (SIG CS___asan_memcpy)) :
  socket_send_c.tsocket_send_spec B MT.
Proof.
exact (socket_send.tsocket_send_holds B MT TXMALLOC AFREE4 AFREE_NULL4 AMEMSET AMEMCPY CmdRecRest.cmd_val_objs_PB HB MTL
  CmdRecRest.cmd_palib CmdRecRest.cmd_sig_prog_PB CmdRecImg.cmd_img_facts_tfib (CmdRecRest.cmd_prw_tfib B HB)).
Qed.
End closed.
Print Assumptions tsocket_send_closed.
