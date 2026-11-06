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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaSB PaDenot PaLibG PaLibH PaCall CmdBase CmdRep CmdObj CmdZsh CmdAddr CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c arg_i_c arg_line_c answer_c sup_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
sup_call_s0 sup_call_s1 sup_call_s3 sup_call_a sup_call_b sup_call_t.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* the statement's callee contracts, at every FP state, and bridge (sup_call_c.v:63-68) *)
Hypothesis TREC_CALLS_FREE : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the per-binary record *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
(* the image's per-binary facts *)
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis PRW : prog_rw SEGS B.

(* the line's block is none of the recorder's: the statement's block premise says the line is apart from every
   block of O, and a block holding the line cannot be apart from it *)
Lemma sc_line_blk_of : forall ly S O pl (line : list byte),
  in_blockA (ablocks B ly S) pl (Z.of_nat (length line) + 1) ->
  Forall (fun qk => iv_apart pl (Z.of_nat (length line) + 1) (fst qk) (snd qk)) O ->
  sc_line_blk B ly S O pl line.
Proof.
intros ly S O pl line (p & k & Hpk & Hp & Hk) HAP.
pose proof (Zle_0_nat (length line)) as Hlen0.
exists p, k. split; [exact Hpk|]. split; [|split; lia].
intros HO. rewrite Forall_forall in HAP. specialize (HAP (p, k) HO). cbn [fst snd] in HAP.
unfold iv_apart in HAP. lia.
Qed.

Theorem tsup_call_holds : tsup_call_spec B MT.
Proof.
unfold tsup_call_spec.
intros ly S W regs mem md ch id pl line R O.
set (t := snd (sup_call_m R id line)).
intros HPRE HFRM HFR HROD HRO H10 Hid H11 Hpl HLINE HREP HEV HLIVE HMO.
pose proof HLINE as (HBLK & HAP & HSTRL & HLEN).
assert (HP : sc_pre B MT ly S W regs mem md ch id pl line R O t).
{ unfold sc_pre. split; [exact HPRE|]. split; [exact HFRM|]. split; [exact HFR|]. split; [exact HROD|].
  split; [exact HRO|]. split; [exact H10|]. split; [exact Hid|]. split; [exact H11|]. split; [exact Hpl|].
  split; [exact HLINE|]. split; [exact HREP|]. split; [exact HEV|]. split; [exact HLIVE | exact HMO]. }
pose proof (sc_line_blk_of ly S O pl line HBLK HAP) as HLB.
change (SRr SEGS W (cfg_at SEGS (BASE + AF_sup_call) regs mem md)
  (sc_post B MT ly S W regs mem md id line R O t)).
exact (sc_prologue B MT TREC_CALLS_FREE VOBJS HB LAWS TL MTL SIGP IMG PRW
  (sc_body B MT TARG_I TARG_LINE VOBJS HB LAWS MTL SIGP IMG PRW
    (fun fx0 => sc_tail_ok (fx := fx0) B MT TANSWER HB LAWS MTL IMG))
  ly S W regs mem md ch id pl line R O HP HLB).
Qed.
End e.
End f.
End w.

About tsup_call_holds.
Print Assumptions tsup_call_holds.
