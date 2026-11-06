(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of sup_reply_code (plugin-hostd/fuzz_command, 0x89d6c, 20 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (pb_cmpPixel, a leaf that ends in a tail jump to a runtime entry) and A/ACh2.v (the step through a call and back). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_reply_code.v, with its module names changed; 63 of its 100 lines of code are new or changed and 251 lines of the source are left out. *)
(* check_words' ASan walk (plugin-hostd/fuzz_command, entry 0x878b4, 405 instructions): the theorem.
   tcheck_words_ok proves tcheck_words_spec (check_words_c.v) as stated, from the segment lemmas of
   check_words_sA.v .. check_words_sR.v and the loop assembly of check_words_asm.v (the cut points and the segments'
   statements are in check_words_d.v); the record facts the segment files carry as Section hypotheses are discharged
   from CmdRecFacts by check_words_rf.v, so the theorem names only the statement's hypotheses and the per-binary
   walk hypotheses, with cgif's names. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts check_words_d check_words_rf.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_asm
check_words_sA check_words_sJB check_words_sC check_words_sI1 check_words_sI2 check_words_sI3 check_words_sD check_words_sR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's hypotheses (check_words_c.v), word for word: callees and runtime
   entries at every FP state (passes 4, 4b) *)
Hypothesis HJOINED : forall fx0 : YK11.FPState, @tjoined_spec fx0 rc SK PI B MT.
Hypothesis HADD : forall fx0 : YK11.FPState, @tcheck_words_add_spec fx0 rc SK PI B MT.
Hypothesis HCHAIN : forall fx0 : YK11.FPState, @tcheck_words_chain_spec fx0 rc SK PI B MT.
Hypothesis HPIN : forall fx0 : YK11.FPState, @tcwps_spec fx0 rc SK PI B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASMALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASTRSPN : forall fx0 : YK11.FPState, @astrspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8.
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis AATOI : forall fx0 : YK11.FPState, @aatoi_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
(* the per-binary walk facts *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis SIGP : cmd_sig_prog.
(* a segment lemma at the FP state fx0: its hypotheses are the statement's at fx0, the record facts, and the
   statements of the points it goes on to (at fx0, or at every FP state for I2 and D) *)
Ltac cw_at_fx L fx0 :=
  unfold G_J, G_P1, G_LH, G_IH, G_IK, G_ICMP, G_ICMP2, G_IL, G_D, G_REL, G_ENTRY in *;
  pose proof (HJOINED fx0) as HJOINED0; pose proof (HADD fx0) as HADD0; pose proof (HCHAIN fx0) as HCHAIN0;
  pose proof (HPIN fx0) as HPIN0; pose proof (AFREE4 fx0) as AFREE40; pose proof (ASMALLOC0 fx0) as ASMALLOC00;
  pose proof (ASTRSPN fx0) as ASTRSPN0; pose proof (ASTRCSPN fx0) as ASTRCSPN0; pose proof (ASTRCMP fx0) as ASTRCMP0;
  pose proof (AATOI fx0) as AATOI0; pose proof (ASNPRINTF fx0) as ASNPRINTF0;
  apply (L fx0);
  first [ assumption
        | match goal with H : forall fx1 : YK11.FPState, _ |- _ => exact (H fx0) end
        | match goal with H : forall fx1 : YK11.FPState, _ |- _ => exact H end ].
Theorem tcheck_words_ok : tcheck_words_spec B MT.
Proof.
(* the segment files' record-fact hypotheses, from CmdRecFacts *)
pose proof (cw_rf_rro B IMG) as RRO.
pose proof (cw_rf_rec_cells B LAWS HB IMG) as cmd_rec_cells.
pose proof (cw_rf_rom_view_on B LAWS HB IMG) as cmd_rom_view_on.
pose proof (cw_rf_heap_tail_vis B LAWS HB) as cmd_heap_tail_vis.
pose proof (cw_rf_prog_unowned B LAWS HB IMG) as cmd_prog_unowned.
pose proof (cw_rf_zsh B LAWS HB) as ZSH_cw.
pose proof (cw_rf_ro_unowned B IMG) as cw_ro_unowned.
pose proof (cw_rf_tail_vis B LAWS HB IMG) as cmd_tail_vis.
pose proof (cmd_ro_ok_of_aro SEGS B LAWS HB IMG) as cmd_ro_ok_of_aro.
apply cw_assemble.
- intros H fx0. cw_at_fx (fun fx1 => @seg_A fx1) fx0.
- intros H fx0. cw_at_fx (fun fx1 => @seg_J fx1) fx0.
- intros H1 H2 fx0. cw_at_fx (fun fx1 => @seg_B fx1) fx0.
- intros c H1 H2 fx0. cw_at_fx (fun fx1 => @seg_C fx1) fx0.
- intros c a H1 H2 fx0. cw_at_fx (fun fx1 => @seg_I1h fx1) fx0.
- intros c a H1 H2 fx0. cw_at_fx (fun fx1 => @seg_I1l fx1) fx0.
- intros c a H1 H2 H3 fx0. cw_at_fx (fun fx1 => @seg_I2 fx1) fx0.
- intros c a H1 fx0. cw_at_fx (fun fx1 => @seg_I3a fx1) fx0.
- intros c a H1 fx0. cw_at_fx (fun fx1 => @seg_I3b fx1) fx0.
- intros c H1 H2 fx0. cw_at_fx (fun fx1 => @seg_D fx1) fx0.
- intros fx0. cw_at_fx (fun fx1 => @seg_R fx1) fx0.
Qed.
End e.
End f.
End d.
