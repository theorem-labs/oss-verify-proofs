(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of answer (plugin-hostd/fuzz_command, 0x8a4c0, 198 instructions), assembled in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v (pb_cgif_closeX from the segment lemmas): the entry to BODY (answer_e.v), BODY to JOIN and HEAD (answer_br.v), syntax_instantiate's loop from HEAD to JOIN (answer_l.v), and JOIN to the return (answer_t.v); the cut statements and the entry context are lib/A/Prog/answer_s1.v. *)
(* Modified by Theorem Labs, 2026-10: re-fitted to statement passes 4, 4b and 5: the callee and runtime contracts at every FP state, the rounding-mode premise passed to BODY, the FP-existential post; JOIN is used at every FP state. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/answer.v, with its module paths, module names and addresses changed; 30 of its 62 lines of code are new or changed and 31 lines of the source are left out. *)
(* sup_remove's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan,
   BASE + AF_sup_remove = 0x8b258, 119 instructions, 103 walked): the statement tsup_remove_spec
   (lib/B/Prog/sup_remove_c.v) proved by composing the four segments and the post's
   composition (sup_remove_s1.v gives their statements):
   - sr_g1 (sup_remove_g1.v): entry .. the class-0 frame's take (0x8b2b8) .. record(2) (0x8b350), under sr_g2_stmt;
   - sr_g2 (sup_remove_g2.v): record's return .. snprintf(b, 16, "%d", id) (0x8b374), under sr_g3_stmt at the FP
     state the wrapper returns;
   - sr_g3 (sup_remove_g3.v): the wrapper's return .. arg_s(c, b) (0x8b380) .. answer(c, "resp 0", 1) (0x8b39c),
     under sr_g4_stmt at the FP state answer returns and sr_q_stmt;
   - sr_g4 (sup_remove_g4.v): answer's return .. the frame's release .. `ret` (0x8b430);
   - sr_q (sup_remove_q.v): the post at answer's return from record's, arg_s's and answer's posts.
   The walk hypotheses have cgif's names (HB, LAWS, TL, TLF, MTL, MTFL, FFL, IMG, SIGP); three more the
   segments take are closed here: ML from the allocator universe of the entry's AR state (YG05.model_laws_ok),
   SMP by YG05.stack_malloc_progress, ASF by YG0t.astack_free_law_ok. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG05 YG0t.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdPaLib PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c answer_c sup_remove_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_remove_s1 sup_remove_q sup_remove_g1 sup_remove_g2 sup_remove_g3 sup_remove_g4.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase.
Import ListNotations.
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
(* the statement's Section hypotheses (sup_remove_c.v:88-93), word for word *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.
Hypothesis SIGP : cmd_sig_prog.

Theorem tsup_remove_spec_holds : tsup_remove_spec B MT.
Proof.
(* intros straight on the statement, so its `let t` stays a local definition *)
intros ly S W regs mem md ch id R O t HPRE.
(* ML from the allocator universe of the entry's AR state; SMP and ASF hold of every record *)
pose proof (am_universe _ _ _ _ (proj1 (proj1 HPRE))) as HU.
pose proof (YG05.model_laws_ok _ HU) as ML.
assert (SMP : stack_malloc_progressP B)
  by (intros s cid HW Hc Hn; exact (YG05.stack_malloc_progress (as_universe B) s cid HW Hc Hn)).
pose proof (YG0t.astack_free_law_ok SEGS B) as ASF.
revert HPRE.
exact (@sr_g1 fx rc SK PI B MT TRECORD ASTACK_MALLOC0
  (@sr_g2 fx rc SK PI B MT ASNPRINTF VOBJS HB LAWS IMG
    (fun fx0 : YK11.FPState => @sr_g3 fx0 rc SK PI B MT TARG_S TANSWER VOBJS HB LAWS MTL IMG SIGP
      (fun fx1 : YK11.FPState => @sr_g4 fx1 rc SK PI B MT LAWS ML MTFL ASF FFL IMG)
      (@sr_q rc PI B MT LAWS MTL)))
  HB LAWS TL TLF ML SMP MTL MTFL IMG SIGP ly S W regs mem md ch id R O).
Qed.
End e.
End f.
End d.
