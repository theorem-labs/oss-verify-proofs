(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: sup_call's ASan walk (plugin-hostd/fuzz_command, 0x8a95c, 67 instructions),
   assembled from its three parts (sup_call_s3.v): the prologue to the join of record()'s two arms (sup_call_a.v
   sc_prologue), the body to answer's entry (sup_call_b.v sc_body) and the tail through answer's contract
   (sup_call_t.v sc_tail_ok).

   The theorem is sup_call_c.v's tsup_call_spec as the statement states it (statement
   passes 4, 4b and 5): the line is a live block that is none of the recorder's (in_blockA + iv_apart against O),
   the entry carries rounding mode 0, the post is FP-existential (apost_baseF) and carries the live-bytes bound and
   the settled freshness conjunct, and the callee contracts hold at every FP state. The parts take the image's
   per-binary facts as IMG and PRW and apply CmdRecFacts' lemmas (CmdRecBase.v, CmdRecCells.v, CmdRecRo.v) by
   exact. The body applies the tail at the FP state arg_i returns (sup_call_b.v sc_body), so the tail goes in as
   sc_tail_ok at every FP state. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_call.v, with its module paths and module names changed; 35 of its 62 lines of code are new or changed and 77 lines of the source are left out. *)
(* sup_remove's walk on the ASan build of plugin-hostd/fuzz_command: the statement tsup_remove_spec
   (lib/A/Prog/sup_remove_c.v) proved. The table holds fewer than 16 calls (sr_arm_slot, sup_remove_a.v) or exactly 16
   (sr_arm_spill, sup_remove_p.v: CmdRep's arep_at bounds ncalls by 16, sr_ncalls in sup_remove_r.v); both arms take
   the join piece sr_jl (sup_remove_j.v) and the tail piece sr_tail (sup_remove_t.v). The per-binary facts are Section
   hypotheses with cgif's names (HB, LAWS, TL, MTL, VOBJS, SIGP, PRW, IMG); the pieces' Section hypotheses
   cif_prog_img, RPG, RRO, cmd_ro_in_img and cmd_ro_ok_of_aro are discharged here from IMG : cmd_img_facts SEGS B by
   the field and the lemmas of the same names in lib/A/Prog/CmdRecBase.v and CmdRecRo.v.

   Statement passes 4 and 5: the callees' contracts hold at every FP state
   (forall fx0); the rounding-mode-0 premise HFRM goes to both arms; the tail piece is supplied at every FP state,
   since the arms apply it at the fx1 arg_i returns. astack_pres is gone. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c arg_i_c answer_c sup_remove_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_remove_s1 sup_remove_r sup_remove_q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_remove_j sup_remove_t sup_remove_a sup_remove_p.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require CmdRecBase CmdRecRo.
Import ListNotations.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's Section hypotheses (sup_remove_c.v:63-66) *)
Hypothesis TREC_CALLS_FREE : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis IMG : CmdRecBase.cmd_img_facts SEGS B.

Theorem tsup_remove_spec_holds : tsup_remove_spec B MT.
Proof.
pose proof (CmdRecBase.cif_prog_img _ _ IMG) as cif_prog_img.
pose proof (CmdRecRo.RPG SEGS B LAWS HB IMG) as RPG.
pose proof (CmdRecRo.RRO SEGS B LAWS HB IMG) as RRO.
pose proof (CmdRecRo.cmd_ro_in_img SEGS B LAWS HB IMG) as cmd_ro_in_img.
pose proof (CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG) as cmd_ro_ok_of_aro.
pose proof (sr_jl B MT HB LAWS VOBJS SIGP cif_prog_img PRW RPG RRO cmd_ro_ok_of_aro TARG_I) as JL.
pose proof (fun fx0 : YK11.FPState => sr_tail (fx := fx0) B MT HB LAWS MTL SIGP cif_prog_img RPG RRO cmd_ro_in_img
  cmd_ro_ok_of_aro TANSWER) as TAIL.
(* intros straight on the statement, so its `let t` stays a local definition *)
intros ly S W regs mem md ch id R O t HPRE HFRM Hfr HROD HRO H10 Hid HREP Hev Hlive MOK.
pose proof HREP as (Q & HQ & _).
destruct (sr_ncalls _ _ _ _ _ _ HQ) as [_ Hn16].
destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hlt | Hge].
- exact (sr_arm_slot B MT HB LAWS TL MTL VOBJS cif_prog_img PRW JL TAIL
    ly S W regs mem md ch id R O HPRE HFRM Hfr HROD HRO H10 Hid HREP Hev Hlive MOK Hlt).
- exact (sr_arm_spill B MT HB LAWS TL MTL VOBJS SIGP cif_prog_img PRW RPG RRO TREC_CALLS_FREE JL TAIL
    ly S W regs mem md ch id R O HPRE HFRM Hfr HROD HRO H10 Hid HREP Hev Hlive MOK (Nat.le_antisymm _ _ Hn16 Hge)).
Qed.
End c.
End b.
End a.

Print Assumptions tsup_remove_spec_holds.
Check tsup_remove_spec_holds.
