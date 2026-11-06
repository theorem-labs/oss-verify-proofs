(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of sup_connect on fuzz_command.asan-ubsan (image B, 0x8b45c, 37
   instructions), the B twin of lib/A/Prog/sup_connect.v (a working branch 8d55d5a2288),
   re-derived on B's code: the parts, each proved over the hand-over of sup_connect_s0.v, composed here from
   answer's entry back to sup_connect's entry.
     - sup_connect_s1.v `scb_seg_e`: the entry 0x8b45c, the prologue and record(4), to the return point 0x8b490;
     - sup_connect_s2.v `scb_seg1`: 0x8b490 -> 0x8b49c, arg_s(c, verb);
     - sup_connect_s3.v `scb_seg2`: 0x8b49c -> 0x8b4a8, arg_line(c, line) (RecBridge.v for the raw slot form);
     - sup_connect_s2.v `scb_seg3` and `scb_seg4`: 0x8b4a8 -> 0x8b4b4 -> 0x8b4c0, arg_s(c, port_a), arg_s(c, port_b);
     - sup_connect_s4.v `scb_tail_ok`: the epilogue, `j answer` (0x8b4ec) and answer's contract to the post.
   The interface sup_connect_s0.v states the statement's premises (`scb_pre`) conjunct for conjunct and its post
   (`scb_post`) word for word. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable CmdSyms CmdList CmdPa CmdPaLib CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_s_c arg_line_c answer_c sup_connect_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_connect_s0 sup_connect_s1 sup_connect_s2 sup_connect_s3 sup_connect_s4.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the callees' statements (sup_connect_c.v:80-84) *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the per-binary facts of RULING-STMT.md section 1, which every walk carries (the B twins under A's names) *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.

(* the parts, composed from answer's entry back to sup_connect's entry *)
Lemma scb_walk : SCB_E_stmt B MT.
Proof.
assert (HT : SCB_T_stmt B MT) by (eapply scb_tail_ok; eassumption).
assert (H4 : SCB_4_stmt B MT) by (eapply scb_seg4; eassumption).
assert (H3 : SCB_3_stmt B MT) by (eapply scb_seg3; eassumption).
assert (H2 : SCB_2_stmt B MT) by (eapply scb_seg2; eassumption).
assert (H1 : SCB_1_stmt B MT) by (eapply scb_seg1; eassumption).
eapply scb_seg_e; eassumption.
Qed.

(* sup_connect's statement: its premises are `scb_pre`, conjunct for conjunct, and its post is `scb_post` *)
Theorem tsup_connect_spec_holds : tsup_connect_spec B MT.
Proof.
unfold tsup_connect_spec.
intros ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O. cbv zeta.
intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22.
exact (scb_walk ly S W regs mem md ch pv pl pa pb verb line port_a port_b R O
  (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12
  (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 (conj H20 (conj H21
  H22)))))))))))))))))))))).
Qed.

End e.
End f.
End d.

About tsup_connect_spec_holds.
Print Assumptions tsup_connect_spec_holds.
