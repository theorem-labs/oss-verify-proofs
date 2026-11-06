(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: check_reply's ASan walk (fuzz_command.asan, 0x86d78) assembled from its
   segments, as proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v assembles cgif_close's (pb_cgif_closeX):
     s1 the entry to the memchr call, s2 memchr / check_reply_answer / sup_reply_code, s3 the code's split,
     s4 snprintf, s4b rec_code_declared, s5 strcmp, s6 strlen / rec_shape_of, s7 syntax_reply_matches twice,
     s8 the frame's release and the return.
   snprintf is the only call that changes the FP state, so s4b, s5 and s8 (the segments after it) are taken at every
   FP state and s4 uses them at the state the wrapper returns.
   `pb_check_reply` is tcheck_reply_spec (lib/A/Prog/check_reply_c.v). The walk's facts at the entry that the
   statement no longer states come from its premises: the record's cells (replace_str flag byte, stack guard, errno)
   from CmdRecCells' cmd_rec_cells, the recorder's GOT words from cmd_ro_ok's RO_ptr_a70xx bytes, the read-only
   ranges from CmdRecRo's cmd_ro_in_img, and the words' shadow from AR's zshadow_ok of the stack window
   [ly_stk_lo, ly_stk_hi) (the words lie in it: spZ regs <= w and w + WORDS_W + 12 <= ly_stk_hi ly). The kit lemmas
   take the image facts IMG (cmd_img_facts); the segments take CmdRecImg's cmd_heap_tail_vis, and its
   cmd_prog_unowned and cmd_rom_view_on at IMG, so no record fact is a Section hypothesis (the walk hypotheses keep
   cgif's names; the record facts are lemmas of lib/A/Prog/CmdRecFacts.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 63 of its 97 lines of code are new or changed and 118 lines of the source are left out. *)
(* sup_add's walk on the ASan build of plugin-hostd/fuzz_command: the assembly of its stages.

   The statement is `tsup_add_spec` (lib/A/Prog/sup_add_c.v, after statement passes 4, 4b
   and 5); `sup_add_holds` proves it as stated. Besides the statement's Section hypotheses it takes the walk
   hypotheses, with cgif's names (HB, LAWS, TL, TLF, ML, SMP, MTL, MTFL, ASF, FFL,
   VHIS, SIGP, PRW, IMG). The stages discharge CmdRecFacts' lemmas and cmd_img_facts' fields (cif_prog_img,
   cif_relro_img, cif_prog_not_ro, cmd_ro_in_img, cmd_ro_ok_of_aro, cmd_heap_tail_vis, cmd_tail_vis_at, cmd_rec_cells,
   cmd_aread_ok_chk, cmd_consts_view_snp) by exact from IMG, LAWS and HB (lib/A/Prog/CmdRecFacts.v).
   The stages: sup_add_s1.v (entry .. 0x89ee4), sup_add_s2t.v / sup_add_s2s.v (record()'s two arms .. 0x89f48),
   sup_add_s3.v (.. arg_i's call at 0x89fa8), sup_add_s3a.v's sa_a2_ok (arg_i's return 0x89fac .. 0x89fc0),
   sup_add_s4.v (.. 0x8a050), sup_add_s5.v (.. 0x8a0b8 or, refused, .. 0x8a0c4), sup_add_s6.v (.. 0x8a0c4),
   sup_add_s7.v (the epilogue and `ret`); the vocabulary sup_add_s0.v and the shared lemmas sup_add_lem.v.
   The FP state (pass 4, the FP lifts): arg_i, answer and the snprintf wrapper return at some FP
   state fx1 with fxrel fx fx1 (PaFx.v); the stage after such a call is a closed stage lemma applied at fx1, so each
   stage is assembled here at every FP state with rounding mode 0 (frm0), from the last to the first. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaLibF CmdObj CmdRo CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_add_s0 PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require
sup_add_s1 sup_add_s2t sup_add_s2s sup_add_s3a sup_add_s3 sup_add_s4 sup_add_s5 sup_add_s6 sup_add_s7.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
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
Hypothesis VHIS : cmd_val_his.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
(* the image's per-binary facts; the stages apply CmdRecFacts.v's lemmas to it *)
Hypothesis IMG : cmd_img_facts SEGS B.
(* the statement's Section hypotheses (sup_add_c.v:88-96) *)
Hypothesis TREC_CALLS_FREE : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TXSTRDUP : forall fx0 : YK11.FPState, @txstrdup_spec fx0 rc SK PI B MT.
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis THAND_BACK : forall fx0 : YK11.FPState, @thand_back_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
Hypothesis VOBJS : cmd_val_objs.

(* a stage lemma at the FP state fx1 with rounding mode 0 (H1): each premise is a hypothesis of this section, the
   rounding mode, or a later stage's statement, at every FP state with rounding mode 0 (assembled before it) or at
   fx1 *)
Local Ltac sa_stage P fx1 H1 :=
  repeat match type of P with
  | ?A -> _ => lazymatch type of A with Prop =>
      specialize (P ltac:(first [ assumption
        | match goal with Hs : forall _ : YK11.FPState, _ |- _ => first [exact (Hs fx1) | exact (Hs fx1 H1)] end ])) end
  end.

Theorem sup_add_holds : tsup_add_spec B MT.
Proof.
assert (A4 : forall fx1 : YK11.FPState, frm0 fx1 -> SA_M4_stmt (fx := fx1) B MT).
{ intros fx1 H1. pose proof (sup_add_s7.sa_m4_ok (fx := fx1) B MT) as P. sa_stage P fx1 H1. exact P. }
assert (A3b : forall fx1 : YK11.FPState, frm0 fx1 -> SA_M3b_stmt (fx := fx1) B MT).
{ intros fx1 H1. pose proof (sup_add_s6.sa_m3b_ok (fx := fx1) B MT) as P. sa_stage P fx1 H1. exact P. }
assert (A3 : forall fx1 : YK11.FPState, frm0 fx1 -> SA_M3_stmt (fx := fx1) B MT).
{ intros fx1 H1. pose proof (sup_add_s5.sa_m3_ok (fx := fx1) B MT) as P. sa_stage P fx1 H1. exact P. }
assert (A2 : forall fx1 : YK11.FPState, frm0 fx1 -> SA_M2_stmt (fx := fx1) B MT).
{ intros fx1 H1. pose proof (sup_add_s4.sa_m2_ok (fx := fx1) B MT) as P. sa_stage P fx1 H1. exact P. }
assert (AA2 : forall fx1 : YK11.FPState, frm0 fx1 -> sup_add_s3a.SA_A2_stmt (fx := fx1) B MT).
{ intros fx1 H1. pose proof (sup_add_s3a.sa_a2_ok (fx := fx1) B MT) as P. sa_stage P fx1 H1. exact P. }
assert (A1 : forall fx1 : YK11.FPState, frm0 fx1 -> SA_M1_stmt (fx := fx1) B MT).
{ intros fx1 H1. pose proof (sup_add_s3.sa_m1_ok (fx := fx1) B MT) as P. sa_stage P fx1 H1. exact P. }
assert (A0T : forall fx1 : YK11.FPState, frm0 fx1 -> SA_M0T_stmt (fx := fx1) B MT).
{ intros fx1 H1. pose proof (sup_add_s2t.sa_m0t_ok (fx := fx1) B MT) as P. sa_stage P fx1 H1. exact P. }
assert (A0S : forall fx1 : YK11.FPState, frm0 fx1 -> SA_M0S_stmt (fx := fx1) B MT).
{ intros fx1 H1. pose proof (sup_add_s2s.sa_m0s_ok (fx := fx1) B MT) as P. sa_stage P fx1 H1. exact P. }
assert (AE : forall fx1 : YK11.FPState, frm0 fx1 -> SA_ENTRY_stmt (fx := fx1) B MT).
{ intros fx1 H1. pose proof (sup_add_s1.sa_entry_ok (fx := fx1) B MT) as P. sa_stage P fx1 H1. exact P. }
unfold tsup_add_spec.
intros ly S W regs mem md ch pu id pp pc uri placement client R O HPRE HFRM Hfr HROD HRO H10 Hpu H11 Hid H12 Hpp
  H13 Hpc HU HP HPT HC HCT HREP Hev Hlive MOK.
exact (AE fx HFRM ly S W regs mem md ch pu id pp pc (Some uri) placement client R O
  (conj HPRE (conj Hfr (conj HROD (conj HRO (conj H10 (conj Hpu (conj H11 (conj Hid (conj H12 (conj Hpp
  (conj H13 (conj Hpc (conj HU (conj HP (conj HPT (conj HC (conj HCT (conj HREP (conj Hev (conj Hlive
  MOK))))))))))))))))))))).
Qed.
End e.
End f.
End d.
Print Assumptions sup_add_holds.
