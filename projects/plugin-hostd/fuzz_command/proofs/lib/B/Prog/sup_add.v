(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of answer (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan,
   entry 0x8aa10, 209 instructions, 836 bytes): tanswer_spec of a Theorem Labs lane's lib/B/Prog/answer_c.v (a working branch
   f490061c104), assembled from four segments as the A walk lib/A/Prog/answer.v (a working branch d28426fbb96)
   does: the entry to BODY (answer_e.v), BODY to JOIN and HEAD (answer_br.v, with the snprintf step of answer_snp.v),
   syntax_instantiate's loop from HEAD to JOIN (answer_l.v), and JOIN to the return (answer_t.v); the cut statements
   are answer_s1.v's. B's code differs from A's in the loop (B's registers and its five UBSan trap sites) and in the
   snprintf contract (the shared one, RtPFCmd.asnprintf_sh); the post is apost_baseF: JOIN is used at the FP state the
   snprintf call returns on the refused arm and at the entry's FP state on the loop's exit.
   Report / trap / abort edges, each refuted at its branch (the segment files say where and from what):
   0x8abac (beqz s3, UBSan) in answer_bm.v; 0x8ac08, 0x8ac38, 0x8ac64, 0x8ac80 (UBSan), 0x8ac6c -> 0x8ad50
   (__asan_report_load1), 0x8ac78 -> 0x8ac7c and 0x8ad44 -> 0x8ad48 (__asan_report_store1), 0x8ac34 and 0x8aca0
   (abort) in answer_l.v. The entry's and the tail's branches (0x8aa7c, 0x8aa9c, 0x8acc8) are decided by the record's
   use-after-return cell and the frame address (answer_e.v, answer_t.v).
   Section hypotheses beyond the statement's: the allocator record HB, the meter's laws MTL and frame laws MTFL, the
   side-stack entries' record TLF (PaLibF), and, in the form a Theorem Labs lane states them only at the pinned image (PI := PB_cmd,
   tfibsegs), cmd_palib, cmd_sig_prog_PB, cmd_img_facts_tfib and cmd_frame_flag_law; PRW for the store into
   g_rec.state. AnswerClosed.v discharges all of them but HB, MTL and MTFL at the pinned image. Base: a Theorem Labs lane
   fc8bcbd8b42 (the snprintf contract's band premise `+ 8`, discharged in answer_snp.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/answer.v; 51 of its 81 lines of code are new or changed and 52 lines of the source are left out. *)
(* sup_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan): the assembly of
   its stages.

   The statement is `tsup_add_spec` (lib/B/Prog/sup_add_c.v, a working branch 49d1443048c, statement pass 5);
   `sup_add_holds` proves it as stated. Besides the statement's Section hypotheses it takes the walk hypotheses of
   a Theorem Labs lane's ruling (a Theorem Labs lane's RULING-STMT.md section 1: HB, TL, TLF, ML, SMP, MTL, MTFL, ASF, FFL, SIGP, PRW, IMG);
   AR_laws is the theorem AR_laws_ok (lib/Reusable/YG0q.v). SupAddClosed.v discharges the per-binary ones at the
   pinned image. The B twin of the A walk (lib/A/Prog/sup_add.v on a working branch).
   The stages (program points in sup_add_s0.v): sup_add_s1.v (entry .. record .. M1), sup_add_s2.v (.. arg_s(c, uri)
   .. M2), sup_add_s3.v (.. snprintf "%d" .. M3), sup_add_s4.v (.. arg_s(c, b) .. M4), sup_add_s5.v (.. arg_s(c,
   placement or "-") .. M5), sup_add_s6.v (.. arg_s(c, client or "-") .. M6), sup_add_s7.v (range check, refusal:
   answer .. M9, or mix_call .. M7), sup_add_s8.v (snprintf "resp %d" .. M8), sup_add_s9.v (hand_back .. M9),
   sup_add_s10.v (the epilogue and `ret`). Each stage lemma is proved at an ambient FP state and takes the next
   stages at every FP state, so the chain below closes them from the epilogue back to the entry. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaLibF CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_s_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_add_s0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require
sup_add_s1 sup_add_s2 sup_add_s3 sup_add_s4 sup_add_s5 sup_add_s6 sup_add_s7 sup_add_s8 sup_add_s9 sup_add_s10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
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
(* the walk hypotheses, a Theorem Labs lane's names (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
(* the image's per-binary facts (RULING-STMT.md section 1); the stages apply CmdRecFacts.v's lemmas to it *)
Hypothesis IMG : cmd_img_facts SEGS B.
(* the statement's Section hypotheses (sup_add_c.v:102-109), at every FP state *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis THAND_BACK : forall fx0 : YK11.FPState, @thand_back_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
(* the record's laws: a theorem on this image *)
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

Theorem sup_add_holds : tsup_add_spec B MT.
Proof.
(* the stages, from the epilogue back to the entry; each at every FP state *)
assert (P9 : SA_M9_stmt B MT) by (intros fx'; eapply sup_add_s10.sa_m9_ok; eassumption).
assert (P8 : SA_M8_stmt B MT) by (intros fx'; eapply sup_add_s9.sa_m8_ok; eassumption).
assert (P7 : SA_M7_stmt B MT) by (intros fx'; eapply sup_add_s8.sa_m7_ok; eassumption).
assert (P6 : SA_M6_stmt B MT) by (intros fx'; eapply sup_add_s7.sa_m6_ok; eassumption).
assert (P5 : SA_M5_stmt B MT) by (intros fx'; eapply sup_add_s6.sa_m5_ok; eassumption).
assert (P4 : SA_M4_stmt B MT) by (intros fx'; eapply sup_add_s5.sa_m4_ok; eassumption).
assert (P3 : SA_M3_stmt B MT) by (intros fx'; eapply sup_add_s4.sa_m3_ok; eassumption).
assert (P2 : SA_M2_stmt B MT) by (intros fx'; eapply sup_add_s3.sa_m2_ok; eassumption).
assert (P1 : SA_M1_stmt B MT) by (intros fx'; eapply sup_add_s2.sa_m1_ok; eassumption).
assert (P0 : SA_ENTRY_stmt B MT) by (intros fx'; eapply sup_add_s1.sa_entry_ok; eassumption).
unfold tsup_add_spec.
intros ly S W regs mem md ch pu id pp pc uri placement client R O HPRE HFRM Hfr HROD HRO H10 Hpu H11 Hid H12
  Hpp H13 Hpc HU HP HPT HC HCT HREP Hev Hlive MOK.
exact (P0 fx ly S W regs mem md ch pu id pp pc (Some uri) placement client R O
  (conj HPRE (conj Hfr (conj HROD (conj HRO (conj H10 (conj Hpu (conj H11 (conj Hid (conj H12 (conj Hpp
  (conj H13 (conj Hpc (conj HU (conj HP (conj HPT (conj HC (conj HCT (conj HREP (conj Hev (conj Hlive
  MOK)))))))))))))))))))) HFRM).
Qed.
End e.
End f.
End d.
Print Assumptions sup_add_holds.
