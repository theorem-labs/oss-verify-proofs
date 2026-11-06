(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the closing pattern of the re-fit to statement passes 4-5 for answer's ASan walk
   (lib/A/Prog/answer.v, tanswer_spec_holds), as lib/A/Prog/SupRemoveAllRefitClosed.v does it for the worked example:
   the per-binary record hypotheses the walk names are discharged at the pinned image (lib/A/Prog/CmdImg.v's instance
   PB_cmd, whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head) by the kit's closing helpers: LAWS is
   the core's AR_laws_ok, TL is cmd_palib, TLF is cmd_palibf, ML is cmd_model_laws, SIGP is cmd_sig_prog_PB, VOBJS is
   cmd_val_objs_PB, PRW is cmd_prw_tfib, IMG is cmd_img_facts_tfib, and the two side-stack runtime laws the walk's frame
   steps name are the kit's cmd_stack_malloc_progress (SMP) and cmd_frame_flag_law (FFL). What remains is HB, the
   meter's laws (MTL, and MTFL for the class-7 side-stack frame) and the callees' and runtime entries' contracts at
   every FP state. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/AnswerClosed.v; 94 of its 123 lines of code are new or changed and 29 lines of the source are left out. *)
(* The closing pattern of the pass-4/5 re-fit for the reply walks on the ASan image: each
   walk's theorem (lib/A/Prog/<fn>.v) with the per-binary record hypotheses it names discharged at the pinned image
   (lib/A/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink head AE2k.tfib_sink_head), as
   SupRemoveAllRefitClosed.v does for sup_remove_all: LAWS is the core's AR_laws_ok, TL is cmd_palib, SIGP is
   cmd_sig_prog_PB, IMG is cmd_img_facts_tfib; send_message's and check_reply's PRW, TLF, ML, SMP, ASF and FFL are
   CmdRecRest's cmd_prw_tfib, cmd_palibf, cmd_model_laws, cmd_stack_malloc_progress, cmd_astack_free_law and
   cmd_frame_flag_law. What remains is the callees' contracts (at every FP state), HB, and send_message's meter laws
   MTL and MTFL. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtFormat RtNumber RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdImg CmdBase CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require rec_code_declared_c check_reply_answer_c
  sup_reply_code_c syntax_reply_matches_c rec_shape_of_c rec_clear_c verbs_receive_c send_message_c check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require rec_code_declared check_reply_answer
  sup_reply_code syntax_reply_matches rec_shape_of send_message check_reply.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Existing Instance CmdImg.PB_cmd | 0.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PB_cmd).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PB_cmd s).
Variable B : asyms.
Variable MT : YC5d.ameter_ops.
(* the allocator record and the meter's laws; send_message's side-stack frame
   also needs the meter's frame laws (MTFL) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : YC5d.ameter_laws MT.
Hypothesis MTFL : YC5d.ameter_fs_laws MT.

(* the statement and walk modules are named by A.Prog: lib/Prog has modules of the same short names *)
Theorem trec_code_declared_closed :
  @A.Prog.rec_code_declared_c.trec_code_declared_spec fx rc AE2k.tfib_sink_head PB_cmd B MT.
Proof.
exact (@A.Prog.rec_code_declared.trec_code_declared_spec_holds fx rc AE2k.tfib_sink_head PB_cmd B MT HB
  (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palib B HB)).
Qed.

Theorem tcheck_reply_answer_closed
  (SRC : forall fx0 : YK11.FPState,
     @A.Prog.sup_reply_code_c.tsup_reply_code_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (ASTRCMP : forall fx0 : YK11.FPState,
     @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp))
  (ASTRCSPN : forall fx0 : YK11.FPState,
     @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) A_SSP_GOT A_SSP_GUARD)
  (ASTRNCMP : forall fx0 : YK11.FPState,
     @astrncmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strncmp)) :
  @A.Prog.check_reply_answer_c.tcheck_reply_answer_spec fx rc AE2k.tfib_sink_head PB_cmd B MT.
Proof.
exact (@A.Prog.check_reply_answer.tcheck_reply_answer_spec_holds fx rc AE2k.tfib_sink_head PB_cmd B MT
  (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palib B HB) HB SRC ASTRCMP ASTRCSPN ASTRNCMP
  (CmdRecImg.cmd_img_facts_tfib B HB) CmdRecRest.cmd_sig_prog_PB).
Qed.

Theorem tsup_reply_code_closed
  (ASTRNCMP : forall fx0 : YK11.FPState,
     @astrncmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strncmp))
  (AATOI : forall fx0 : YK11.FPState,
     @aatoi_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_atoi) A_FLAG_REPLACE_STR A_SSP_GOT A_SSP_GUARD) :
  @A.Prog.sup_reply_code_c.tsup_reply_code_spec fx rc AE2k.tfib_sink_head PB_cmd B MT.
Proof.
exact (@A.Prog.sup_reply_code.tsup_reply_code_spec_holds fx rc AE2k.tfib_sink_head PB_cmd B MT ASTRNCMP AATOI
  (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palib B HB) HB (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.

Theorem tsyntax_reply_matches_closed
  (ASTRCSPN : forall fx0 : YK11.FPState,
     @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) A_SSP_GOT A_SSP_GUARD)
  (ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_bcmp)) :
  @A.Prog.syntax_reply_matches_c.tsyntax_reply_matches_spec fx rc AE2k.tfib_sink_head PB_cmd B MT.
Proof.
exact (@A.Prog.syntax_reply_matches.tsyntax_reply_matches_spec_holds fx rc AE2k.tfib_sink_head PB_cmd B MT
  ASTRCSPN ABCMP (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palib B HB) HB (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.

Theorem trec_shape_of_closed
  (ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen))
  (ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_bcmp)) :
  @A.Prog.rec_shape_of_c.trec_shape_of_spec fx rc AE2k.tfib_sink_head PB_cmd B MT.
Proof.
exact (@A.Prog.rec_shape_of.trec_shape_of_spec_holds fx rc AE2k.tfib_sink_head PB_cmd B MT ASTRLEN ABCMP HB
  (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palib B HB) (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.

Theorem tsend_message_closed
  (RCL : forall fx0 : YK11.FPState, @A.Prog.rec_clear_c.trec_clear_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (VR : forall fx0 : YK11.FPState,
     @A.Prog.verbs_receive_c.tverbs_receive_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (ASM : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1)
  (AMALLOC4 : forall fx0 : YK11.FPState, @YC5d.amalloc04_rule fx0 rc AE2k.tfib_sink_head SEGS B MT)
  (AFREE4 : forall fx0 : YK11.FPState, @YC5d.afree04_rule fx0 rc AE2k.tfib_sink_head SEGS B MT)
  (AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy)) :
  @A.Prog.send_message_c.tsend_message_spec fx rc AE2k.tfib_sink_head PB_cmd B MT.
Proof.
exact (@A.Prog.send_message.tsend_message_spec_holds fx rc AE2k.tfib_sink_head PB_cmd B MT
  (CmdRecRest.cmd_palib B HB) (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palibf B HB) (CmdRecRest.cmd_model_laws B HB)
  (CmdRecRest.cmd_stack_malloc_progress B) MTL MTFL RCL VR ASM (CmdRecRest.cmd_astack_free_law B)
  (CmdRecRest.cmd_frame_flag_law B) AMALLOC4 AFREE4 AMEMCPY CmdRecRest.cmd_sig_prog_PB HB
  (CmdRecRest.cmd_prw_tfib B HB) (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.

Theorem tcheck_reply_closed
  (CRA : forall fx0 : YK11.FPState,
     @A.Prog.check_reply_answer_c.tcheck_reply_answer_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (SRC : forall fx0 : YK11.FPState,
     @A.Prog.sup_reply_code_c.tsup_reply_code_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (RCD : forall fx0 : YK11.FPState,
     @A.Prog.rec_code_declared_c.trec_code_declared_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (RSO : forall fx0 : YK11.FPState,
     @A.Prog.rec_shape_of_c.trec_shape_of_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (SRM : forall fx0 : YK11.FPState,
     @A.Prog.syntax_reply_matches_c.tsyntax_reply_matches_spec fx0 rc AE2k.tfib_sink_head PB_cmd B MT)
  (ASM : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1)
  (AMEMCHR : forall fx0 : YK11.FPState,
     @amemchr0_nf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_memchr))
  (ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen))
  (ASNPRINTF : forall fx0 : YK11.FPState,
     @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) A_SSP_GOT A_SSP_GUARD)
  (ASTRCMP : forall fx0 : YK11.FPState,
     @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp)) :
  @A.Prog.check_reply_c.tcheck_reply_spec fx rc AE2k.tfib_sink_head PB_cmd B MT.
Proof.
exact (@A.Prog.check_reply.pb_check_reply fx rc AE2k.tfib_sink_head PB_cmd B MT CRA SRC RCD RSO SRM ASM
  (CmdRecRest.cmd_astack_free_law B) (CmdRecRest.cmd_frame_flag_law B) AMEMCHR ASTRLEN ASNPRINTF ASTRCMP
  (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palib B HB) (CmdRecRest.cmd_palibf B HB) (CmdRecRest.cmd_model_laws B HB)
  (CmdRecRest.cmd_stack_malloc_progress B) HB CmdRecRest.cmd_sig_prog_PB (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.
End closed.
