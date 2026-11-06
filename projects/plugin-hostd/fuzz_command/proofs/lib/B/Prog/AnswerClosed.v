(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the closing of answer's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan; lib/B/Prog/answer.v, tanswer_spec_holds) at the pinned image: lib/B/Prog/CmdImg.v's
   instance PB_cmd, whose segments are tfibsegs, and the sink head YE2k.tfib_sink_head. The pattern of
   a Theorem Labs lane's PASS4-REFIT.md section F (A's lib/A/Prog/SupRemoveAllRefitClosed.v:29-60 on a working branch e84227c9553,
   a Theorem Labs lane's lib/A/Prog/RecBClosed.v:48-90, :163-191 on a working branch f349bdaedba), with a Theorem Labs lane's B
   CmdRecFacts (a working branch fc8bcbd8b42, with 707acd856cb's closers): the walk's per-binary image facts are
   CmdRecImg.cmd_img_facts_tfib, its object bridge CmdRecRest.cmd_val_objs_PB, its call targets
   CmdRecRest.cmd_sig_prog_PB, the shadow base's record CmdRecRest.cmd_palib, PRW CmdRecRest.cmd_prw_tfib (the
   program's statics in tfibsegs' read-write window), TLF (PaLibF.PALibF) CmdRecRest.cmd_palibf (the record's
   use-after-return cell 0xb0c40 and its GOT word 0xa5fa8, and its code map) and the frame flag law
   CmdRecRest.cmd_frame_flag_law. What remains is the allocator record HB, the meter's laws MTL and frame laws MTFL,
   and the statement's callee and runtime contracts at every FP state. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtStack RtShadow RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecImg CmdRecRest PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require mix_call_c hand_back_c answer_c answer.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PB_cmd s).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record, the meter's laws and its frame laws (a Theorem Labs lane's RULING-STMT.md section 1; the class-7
   side-stack frame changes the state by set_fs) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTFL : YC5d.ameter_fs_laws MT.
Theorem tanswer_closed
  (THAND_BACK : forall fx0 : YK11.FPState, @hand_back_c.thand_back_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (TMIX_CALL : forall fx0 : YK11.FPState, @mix_call_c.tmix_call_spec fx0 rc YE2k.tfib_sink_head PB_cmd B MT)
  (ASTACK_MALLOC7 : forall fx0 : YK11.FPState,
     @astack_malloc_sz_realizes fx0 rc SEGS B (SIG CS___asan_stack_malloc_7) 7)
  (ASTACK_FREE7 : forall fx0 : YK11.FPState, @astack_free_realizes fx0 rc SEGS B (SIG CS___asan_stack_free_7) 7)
  (ASET_SHADOW00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_00) 0)
  (ASET_SHADOWF8 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f8) 0xf8)
  (ASNPRINTF : forall fx0 : YK11.FPState,
     @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158) :
  @answer_c.tanswer_spec fx rc YE2k.tfib_sink_head PB_cmd B MT.
Proof.
exact (@answer.tanswer_spec_holds fx rc YE2k.tfib_sink_head PB_cmd B MT THAND_BACK TMIX_CALL ASTACK_MALLOC7 ASTACK_FREE7
  ASET_SHADOW00 ASET_SHADOWF8 ASNPRINTF CmdRecRest.cmd_val_objs_PB HB MTL MTFL (CmdRecRest.cmd_palibf B HB)
  CmdRecRest.cmd_palib CmdRecRest.cmd_sig_prog_PB (CmdRecRest.cmd_prw_tfib B HB) CmdRecImg.cmd_img_facts_tfib
  CmdRecRest.cmd_frame_flag_law).
Qed.
End closed.

About tanswer_closed.
Print Assumptions tanswer_closed.
