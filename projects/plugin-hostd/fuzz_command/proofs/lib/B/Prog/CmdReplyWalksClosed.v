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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/CmdReplyWalksClosed.v, with its module paths and module names changed; 55 of its 105 lines of code are new or changed and 73 lines of the source are left out. *)
(* The closing pattern of a Theorem Labs lane's PASS4-REFIT.md section F on the ASan+UBSan build fuzz_command.asan-ubsan (lib/B),
   for the B walks of the reply checks and send_message: rec_code_declared, sup_reply_code, syntax_reply_matches,
   check_reply_answer, rec_shape_of, send_message (lib/B/Prog/<fn>.v, t<fn>_spec_holds) and check_reply
   (lib/B/Prog/check_reply.v, pb_check_reply). Each walk's per-binary record hypotheses are discharged at the pinned
   image (lib/B/Prog/CmdImg.v's instance PB_cmd, whose segments are tfibsegs, and the sink head YE2k.tfib_sink_head),
   as lib/A/Prog/SupRemoveAllRefitClosed.v does on A: LAWS is the core's AR_laws_ok (Reusable/YG0q.v), TL is cmd_palib
   and SIGP is cmd_sig_prog_PB (lib/B/Prog/CmdRecRest.v), IMG is cmd_img_facts_tfib (lib/B/Prog/CmdRecImg.v);
   send_message's and check_reply's TLF, ML, SMP, ASF and FFL, and send_message's PRW, are CmdRecRest's cmd_palibf,
   cmd_model_laws, cmd_stack_malloc_progress, cmd_astack_free_law, cmd_frame_flag_law and cmd_prw_tfib (the A
   kit's names). What remains is HB, each statement's callee and runtime-entry contracts (at every FP state), and
   send_message's meter laws MTL and MTFL. Every instance is named at each use: SK and PI below. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0f YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib CmdObj CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecImg CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require rec_code_declared_c sup_reply_code_c
  syntax_reply_matches_c check_reply_answer_c rec_shape_of_c rec_clear_c verbs_receive_c send_message_c check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require rec_code_declared sup_reply_code
  syntax_reply_matches check_reply_answer rec_shape_of send_message check_reply.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SK := YE2k.tfib_sink_head.
#[local] Notation PI := (@CmdImg.PB_cmd rc).
#[local] Notation SEGS := (@pa_segs rc cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma rc cmd_listing PI s).
Variable B : asyms.
Variable MT : ameter_ops.
(* the allocator record and the meter's laws (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.

Theorem trec_code_declared_closed : @B.Prog.rec_code_declared_c.trec_code_declared_spec fx rc SK PI B MT.
Proof.
exact (@B.Prog.rec_code_declared.trec_code_declared_spec_holds fx rc SK PI B MT HB (YG0q.AR_laws_ok SEGS B)
  (CmdRecRest.cmd_palib B HB)).
Qed.

Theorem tsup_reply_code_closed
  (ASTRNCMP : forall fx0 : YK11.FPState, @astrncmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strncmp))
  (AATOI : forall fx0 : YK11.FPState,
     @aatoi_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_atoi) A_FLAG_REPLACE_STR A_SSP_GOT A_SSP_GUARD) :
  @B.Prog.sup_reply_code_c.tsup_reply_code_spec fx rc SK PI B MT.
Proof.
exact (@B.Prog.sup_reply_code.tsup_reply_code_spec_holds fx rc SK PI B MT ASTRNCMP AATOI HB
  (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palib B HB) (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.

Theorem tsyntax_reply_matches_closed
  (ASTRCSPN : forall fx0 : YK11.FPState,
     @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) A_SSP_GOT A_SSP_GUARD)
  (ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_bcmp)) :
  @B.Prog.syntax_reply_matches_c.tsyntax_reply_matches_spec fx rc SK PI B MT.
Proof.
exact (@B.Prog.syntax_reply_matches.tsyntax_reply_matches_spec_holds fx rc SK PI B MT ASTRCSPN ABCMP
  (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palib B HB) HB (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.

Theorem tcheck_reply_answer_closed
  (SRC : forall fx0 : YK11.FPState, @B.Prog.sup_reply_code_c.tsup_reply_code_spec fx0 rc SK PI B MT)
  (ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp))
  (ASTRCSPN : forall fx0 : YK11.FPState,
     @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) A_SSP_GOT A_SSP_GUARD)
  (ASTRNCMP : forall fx0 : YK11.FPState, @astrncmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strncmp)) :
  @B.Prog.check_reply_answer_c.tcheck_reply_answer_spec fx rc SK PI B MT.
Proof.
exact (@B.Prog.check_reply_answer.tcheck_reply_answer_spec_holds fx rc SK PI B MT (YG0q.AR_laws_ok SEGS B)
  (CmdRecRest.cmd_palib B HB) HB SRC ASTRCMP ASTRCSPN ASTRNCMP (CmdRecImg.cmd_img_facts_tfib B HB)
  CmdRecRest.cmd_sig_prog_PB).
Qed.

Theorem trec_shape_of_closed
  (ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen))
  (ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_bcmp)) :
  @B.Prog.rec_shape_of_c.trec_shape_of_spec fx rc SK PI B MT.
Proof.
exact (@B.Prog.rec_shape_of.trec_shape_of_spec_holds fx rc SK PI B MT ASTRLEN ABCMP (YG0q.AR_laws_ok SEGS B) HB
  (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.

Theorem tsend_message_closed
  (RCL : forall fx0 : YK11.FPState, @B.Prog.rec_clear_c.trec_clear_spec fx0 rc SK PI B MT)
  (VR : forall fx0 : YK11.FPState, @B.Prog.verbs_receive_c.tverbs_receive_spec fx0 rc SK PI B MT)
  (ASM : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1)
  (AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT)
  (AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT)
  (AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy)) :
  @B.Prog.send_message_c.tsend_message_spec fx rc SK PI B MT.
Proof.
exact (@B.Prog.send_message.tsend_message_spec_holds fx rc SK PI B MT (CmdRecRest.cmd_palib B HB)
  (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palibf B HB) (CmdRecRest.cmd_model_laws B HB)
  (CmdRecRest.cmd_stack_malloc_progress B) MTL MTFL RCL VR ASM (CmdRecRest.cmd_astack_free_law B)
  (CmdRecRest.cmd_frame_flag_law B) AMALLOC4 AFREE4 AMEMCPY CmdRecRest.cmd_sig_prog_PB HB
  (CmdRecRest.cmd_prw_tfib B HB) (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.

Theorem tcheck_reply_closed
  (CRA : forall fx0 : YK11.FPState, @B.Prog.check_reply_answer_c.tcheck_reply_answer_spec fx0 rc SK PI B MT)
  (SRC : forall fx0 : YK11.FPState, @B.Prog.sup_reply_code_c.tsup_reply_code_spec fx0 rc SK PI B MT)
  (RCD : forall fx0 : YK11.FPState, @B.Prog.rec_code_declared_c.trec_code_declared_spec fx0 rc SK PI B MT)
  (RSO : forall fx0 : YK11.FPState, @B.Prog.rec_shape_of_c.trec_shape_of_spec fx0 rc SK PI B MT)
  (SRM : forall fx0 : YK11.FPState, @B.Prog.syntax_reply_matches_c.tsyntax_reply_matches_spec fx0 rc SK PI B MT)
  (ASM : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1)
  (AMEMCHR : forall fx0 : YK11.FPState,
     @amemchr0_nf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_memchr))
  (ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen))
  (ASNPRINTF : forall fx0 : YK11.FPState,
     @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) A_SSP_GOT A_SSP_GUARD)
  (ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp)) :
  @B.Prog.check_reply_c.tcheck_reply_spec fx rc SK PI B MT.
Proof.
exact (@B.Prog.check_reply.pb_check_reply fx rc SK PI B MT CRA SRC RCD RSO SRM ASM
  (CmdRecRest.cmd_astack_free_law B) (CmdRecRest.cmd_frame_flag_law B) AMEMCHR ASTRLEN ASNPRINTF ASTRCMP
  (YG0q.AR_laws_ok SEGS B) (CmdRecRest.cmd_palib B HB) (CmdRecRest.cmd_palibf B HB) (CmdRecRest.cmd_model_laws B HB)
  (CmdRecRest.cmd_stack_malloc_progress B) HB CmdRecRest.cmd_sig_prog_PB (CmdRecImg.cmd_img_facts_tfib B HB)).
Qed.
End closed.
