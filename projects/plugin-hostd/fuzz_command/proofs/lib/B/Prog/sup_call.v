(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of answer (plugin-hostd/fuzz_command, 0x8a4c0, 198 instructions), assembled in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v (pb_cgif_closeX from the segment lemmas): the entry to BODY (answer_e.v), BODY to JOIN and HEAD (answer_br.v), syntax_instantiate's loop from HEAD to JOIN (answer_l.v), and JOIN to the return (answer_t.v); the cut statements and the entry context are lib/A/Prog/answer_s1.v. *)
(* Modified by Theorem Labs, 2026-10: re-fitted to statement passes 4, 4b and 5: the callee and runtime contracts at every FP state, the rounding-mode premise passed to BODY, the FP-existential post; JOIN is used at every FP state. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/answer.v, with its module paths, module names and addresses changed; 34 of its 69 lines of code are new or changed and 28 lines of the source are left out. *)
(* sup_call's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan, entry 0x8af34,
   125 instructions; 109 on the side-stack path walked), assembled from its four parts (sup_call_s3.v): the frame and
   the side-stack frame up to 0x8b030 (sup_call_a.v sc_stage_a), record and the snprintf wrapper (sup_call_b.v
   sc_stage_b), arg_s, arg_line and answer's arguments (sup_call_l.v sc_stage_l), answer and the frame's release
   (sup_call_t.v sc_stage_t).

   The theorem is sup_call_c.v's tsup_call_spec as the statement states it, under the
   statement's Section hypotheses and the walk hypotheses, with cgif's names that the parts use. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo CmdPaLib PaLibF PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c arg_line_c answer_c sup_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_call_s3 sup_call_a sup_call_b sup_call_l sup_call_t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's Section hypotheses (sup_call_c.v:87-93), word for word *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses, with cgif's names *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.

Theorem tsup_call_spec_holds : tsup_call_spec B MT.
Proof.
assert (HT : forall fx0 : YK11.FPState, @SC_L_stmt fx0 rc SK PI B MT)
  by (intros fx0; eapply (@sc_stage_t fx0 rc SK PI B MT); eassumption).
assert (HL : forall fx0 : YK11.FPState, @SC_B_stmt fx0 rc SK PI B MT)
  by (intros fx0; eapply (@sc_stage_l fx0 rc SK PI B MT); first [exact (HT fx0) | eassumption]).
assert (HA : @SC_A_stmt fx rc SK PI B MT) by (eapply (@sc_stage_b fx rc SK PI B MT); eassumption).
assert (HM : @SC_main_stmt fx rc SK PI B MT) by (eapply (@sc_stage_a fx rc SK PI B MT); eassumption).
unfold tsup_call_spec.
intros ly S W regs mem md ch id pl line R O. cbv zeta.
intros HPRE HFRM HFR HROD HRO H10 Hid H11 Hpl HLINE HREP HEV HLIVE HMO.
exact (HM ly S W regs mem md ch id pl line R O HFRM
  (conj HPRE (conj HFR (conj HROD (conj HRO (conj H10 (conj Hid (conj H11 (conj Hpl (conj HLINE
  (conj HREP (conj HEV (conj HLIVE HMO))))))))))))).
Qed.
End e.
End f.
End w.
