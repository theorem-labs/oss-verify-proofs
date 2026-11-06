(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of sup_reply_code (plugin-hostd/fuzz_command, 0x89d6c, 20 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (pb_cmpPixel, a leaf that ends in a tail jump to a runtime entry) and A/ACh2.v (the step through a call and back). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_reply_code.v, with its module names changed; 63 of its 100 lines of code are new or changed and 251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words.v, with its module paths, module names and addresses changed; 24 of its 83 lines of code are new or changed and 41 lines of the source are left out. *)
(* check_words' ASan+UBSan walk (plugin-hostd/fuzz_command.asan-ubsan, entry 0x87ae8, 455 instructions): the theorem.
   tcheck_words_proof proves tcheck_words_spec (lib/B/Prog/check_words_c.v) as stated,
   from the segment lemmas of check_words_sA.v .. check_words_sR.v and the loop assembly of check_words_asm.v (the cut
   points and the segments' statements are in check_words_d.v). The B twin of lib/A/Prog/check_words.v.
   The record facts the segment files carry as Section hypotheses are discharged from
   lib/B/Prog/CmdRecFacts.v by check_words_rf.v; LAWS and ML are the base lemmas YG0q.AR_laws_ok and
   YG05.model_laws_ok at the record's universe (as the B walk of number does).
   The theorem names the statement's hypotheses (check_words_c.v:124-141) and the walk
   hypotheses HB, TL, TLF, MTL, MTFL, IMG, SIGP, nothing else. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q YG05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable CmdSyms CmdList CmdPa CmdPaLib PaLibF CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts check_words_d check_words_rf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_asm
check_words_sA check_words_sJB check_words_sC check_words_sI1 check_words_sI2 check_words_sI3 check_words_sD check_words_sR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's hypotheses (check_words_c.v:124-141), word for word *)
Hypothesis HJOINED : forall fx0 : YK11.FPState, @tjoined_spec fx0 rc SK PI B MT.
Hypothesis HADD : forall fx0 : YK11.FPState, @tcheck_words_add_spec fx0 rc SK PI B MT.
Hypothesis HCHAIN : forall fx0 : YK11.FPState, @tcheck_words_chain_spec fx0 rc SK PI B MT.
Hypothesis HPIN : forall fx0 : YK11.FPState, @tcwps_spec fx0 rc SK PI B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASMALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASTRSPN : forall fx0 : YK11.FPState, @astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa6bf8 0x604158.
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa6bf8 0x604158.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis AATOI : forall fx0 : YK11.FPState, @aatoi_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
(* the per-binary walk facts *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Theorem tcheck_words_proof : tcheck_words_spec B MT.
Proof.
pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
pose proof (YG05.model_laws_ok (as_universe B) (ts_universe B HB)) as ML.
(* the segment files' record-fact hypotheses, from CmdRecFacts *)
pose proof (cw_rf_rro B LAWS HB IMG) as RRO.
pose proof (cw_rf_rec_cells B LAWS HB IMG) as cmd_rec_cells.
pose proof (cw_rf_rom_view_on B LAWS HB IMG) as cmd_rom_view_on.
pose proof (cw_rf_heap_tail_vis B LAWS HB) as cmd_heap_tail_vis.
pose proof (cw_rf_prog_unowned B LAWS HB IMG) as cmd_prog_unowned.
pose proof (cw_rf_zsh B LAWS HB) as ZSH_cw.
pose proof (cw_rf_ro_unowned B IMG) as cw_ro_unowned.
pose proof (cw_rf_tail_vis B LAWS HB IMG) as cmd_tail_vis.
pose proof (cw_rf_got_rec B LAWS HB IMG) as cmd_got_rec.
apply cw_assemble.
- intros H fx0. apply (seg_A (fx := fx0) B MT); first [exact (H fx0) | assumption].
- intros H fx0. apply (seg_J (fx := fx0) B MT); first [exact (H fx0) | assumption].
- intros H1 H2 fx0. apply (seg_B (fx := fx0) B MT); first [exact (H1 fx0) | exact (H2 fx0) | assumption].
- intros c H1 H2 fx0. apply (seg_C (fx := fx0) B MT); first [exact (H1 fx0) | exact (H2 fx0) | assumption].
- intros c a H1 H2 fx0. apply (seg_I1h (fx := fx0) B MT); first [exact (H1 fx0) | exact (H2 fx0) | assumption].
- intros c a H1 H2 fx0. apply (seg_I1l (fx := fx0) B MT); first [exact (H1 fx0) | exact (H2 fx0) | assumption].
- intros c a H1 fx0. apply (seg_I2 (fx := fx0) B MT); first [exact H1 | assumption].
- intros c a H1 H2 fx0. apply (seg_I3a (fx := fx0) B MT); first [exact (H1 fx0) | exact (H2 fx0) | assumption].
- intros c a H1 fx0. apply (seg_I3b (fx := fx0) B MT); first [exact (H1 fx0) | assumption].
- intros c H1 H2 fx0. apply (seg_D (fx := fx0) B MT); first [exact H1 | exact H2 | assumption].
- intros fx0. apply (seg_R (fx := fx0) B MT); assumption.
Qed.
End e.
End f.
End d.
