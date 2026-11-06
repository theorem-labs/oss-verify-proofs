(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the prologue of sup_call's ASan walk (plugin-hostd/fuzz_command): the
   16 instructions from the entry to the test of g_rec.ncalls against 16, and the two arms that meet at 0x8a9d0 —
   the table arm (0x8a9b4..0x8a9cc, which writes ncalls and forms the slot) and the spill arm
   (0x8a99c..0x8a9b0, which calls rec_calls_free on record.spill). The arms are stated with a continuation, so
   the walk from the join on is one lemma, used by both. *)
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
PaSB PaDenot PaLibG PaLibH PaCall PaArt CmdBase CmdRep CmdObj CmdZsh CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c sup_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_call_s1.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the footprint of sup_call, as its statement names it (sup_call_c.v:92-93) *)
Definition SC_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
(A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

(* every byte of the footprint that is not a heap block is one of the program's statics *)
Lemma sc_fp_prog : forall O a, inFP (SC_FP O) a -> ~ inFP (ablocks_fp O) a -> inFP cmd_PG a.
Proof.
intros O a (r & Hin & Hr) Hnb. unfold SC_FP in Hin. cbn [In] in Hin.
unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_STATE, SC_SIZE in *.
destruct Hin as [<- | [<- | [<- | [<- | Hin]]]]; cbn [fst snd] in Hr.
- exists (6174528, 6174528 + 960). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (6174528, 6174528 + 960). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (6174528, 6174528 + 960). split; [left; reflexivity | cbn [fst snd]; lia].
- exists (6175712, 6175712 + 56). split; [right; left; reflexivity | cbn [fst snd]; lia].
- exfalso. apply Hnb. exists r. split; [exact Hin | exact Hr].
Qed.

Section e.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
(* the image's per-binary facts: cif_prog_img _ _ IMG (CmdRecBase.v) *)
Hypothesis IMG : cmd_img_facts SEGS B.
(* a footprint byte of sup_call that is not a heap block is a program static in the image: the fact awr_byte's
   program-static case asks of a callee's footprint byte at cl_callS_wide (PaNoChain.v) *)
Lemma sc_fp_prog_static : forall O a, inFP (SC_FP O) a -> ~ inFP (ablocks_fp O) a ->
Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Proof.
intros O a Ha Hnb. pose proof (sc_fp_prog O a Ha Hnb) as Hpg.
split; [exact (HPROG B HB a Hpg) | exact (cif_prog_img _ _ IMG a Hpg)].
Qed.
End e.
End f.
End w.
