(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of sup_broadcast (plugin-hostd/fuzz_command, 0x8afa0, 61
   instructions), proving tsup_broadcast_spec of sup_broadcast_c.v. Shape: cgif_file_fuzzer's cgif_close walk
   (A/ACh1.v..ACh8.v, AChc.v): the verified symbolic executor over the position-abstract listing, the two inline
   store4 checks removed by the slot's shadow entry (sup_broadcast_s5.v), the calls of rec_calls_free, arg_line and
   the tail jump to answer through the kit's cl_callS_wide, and the recorder's representation from
   sup_broadcast_s2.v. The head reads g_rec.ncalls and either records in the table's next slot (n < 16,
   sup_broadcast_s7.v) or frees the spill's arguments and records there (n = 16, sup_broadcast_s8.v); the recorder
   never holds more than 16 calls (CmdRep.v's ag1_calls).
   The per-binary facts are Section hypotheses under cgif's names (HB, LAWS, TL,
   MTL, PRW, IMG); the segment files carry the image facts they use under the names of the kit's cmd_img_facts
   fields and CmdRecFacts lemmas (cif_prog_img, cif_prog_not_ro, cif_relro_img, cmd_ro_in_img, cmd_ro_ok_of_aro),
   which this file discharges from IMG (CmdRecBase.v, CmdRecRo.v). VOBJS, SIGP and the callees' statements are the
   statement's own.
   Pass-4/5 re-fit: the callees' statements hold at every FP state (forall fx0) and are used
   at the entry's fx: rec_calls_free and arg_line keep the FP state (apost_base, kit rule cl_callS_wide), answer is
   the last step (sup_broadcast_s3.v's sb_tail, through PaFx.v's cl_callS_wideF), so the post is apost_baseF; the
   rounding-mode-0 premise HFRM goes down to sb_tail for answer's own premise. Statement pass 5 removed astack_pres:
   the walk no longer derives it for its callees. The frame chains the three calls' afn_pre ask come from the walk:
   at rec_calls_free and arg_line s0 = line (a heap pointer below alloc_ceiling, achain_low, the empty chain); at
   answer s0 is the entry s0 (sup_broadcast's own afn_pre chain, sup_broadcast_s3.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibG PaLibH PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase CmdRecRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c arg_line_c answer_c sup_broadcast_c sup_broadcast_s3 sup_broadcast_s7 sup_broadcast_s8.
Import ListNotations.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
(* the image facts (one of CmdRecFacts.v's names; lib/A/Prog/CmdRecBase.v cmd_img_facts) *)
Hypothesis IMG : cmd_img_facts SEGS B.
(* the statement's own hypotheses (sup_broadcast_c.v:63-65), at every FP state *)
Hypothesis TREC_CALLS_FREE : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.

(* the theorem: the head's two arms, split on the number of recorded calls *)
Theorem tsup_broadcast_spec_holds : tsup_broadcast_spec B MT.
Proof.
unfold tsup_broadcast_spec.
intros ly S W regs mem md ch pl line R O HPRE HFRM Hfr8 HROD _ H10 Hpl (HBLK & HAP & HSTR & HLEN) HREC Hev Hlive HMOK.
pose proof HREC as (Q & (_ & _ & _ & (HL16 & _) & _) & _).
destruct (Nat.lt_ge_cases (length (r_calls R)) 16) as [Hlt | Hge].
- exact (sb_head_table B MT HB LAWS TL MTL VOBJS SIGP PRW (cif_prog_img _ _ IMG) (cif_prog_not_ro _ _ IMG)
    (cif_relro_img _ _ IMG) (cmd_ro_in_img SEGS B LAWS HB IMG) (cmd_ro_ok_of_aro SEGS B LAWS HB IMG) TARG_LINE TANSWER
    ly S W regs mem md ch pl line R O HPRE HFRM Hfr8 HROD H10 Hpl HBLK HAP HSTR HLEN HREC Hlt Hev Hlive HMOK).
- exact (sb_head_spill B MT HB LAWS TL MTL VOBJS SIGP PRW (cif_prog_img _ _ IMG) (cif_prog_not_ro _ _ IMG)
    (cif_relro_img _ _ IMG) (cmd_ro_in_img SEGS B LAWS HB IMG) (cmd_ro_ok_of_aro SEGS B LAWS HB IMG) TREC_CALLS_FREE
    TARG_LINE TANSWER
    ly S W regs mem md ch pl line R O HPRE HFRM Hfr8 HROD H10 Hpl HBLK HAP HSTR HLEN HREC
    (Nat.le_antisymm _ _ HL16 Hge) Hev Hlive HMOK).
Qed.

End e.
End f.
End d.
Print Assumptions tsup_broadcast_spec_holds.
