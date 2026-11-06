(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of check_refusal (plugin-hostd/fuzz_command, 0x87f08, 52 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (pb_wcb: entry, branch, return) and A/ACh2.v:122-290 (a program call through cl_callS and back). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_refusal.v, with its module paths and module names changed; 27 of its 65 lines of code are new or changed and 278 lines of the source are left out. *)
(* check_words_add on the ASan build of plugin-hostd/fuzz_command: the proof of tcheck_words_add_spec
   (lib/A/Prog/check_words_add_c.v). The walk is in check_words_add_s4.v (entry 0x88abc .. 0x88b60),
   check_words_add_s2.v / _s3.v (0x88b60 .. 0x88bd0, the literal and the word placement) and
   check_words_add_s2.v (0x88bd0 .. ret). Besides the statement's own Section hypotheses (ASTRCMP, ASTRNCMP), it
   takes the walk hypotheses, with cgif's names, that the five fields of
   check_words_add_s1.v's record CwaFacts need: HB (the allocator record is fuzz_command's, CmdBSyms) and IMG (the
   image facts, cmd_img_facts). lib/A/Prog/CheckWordsAddClosed.v discharges IMG at the pinned image
   (cmd_img_facts_tfib). The fields are lib/A/Prog/
   CmdRecFacts.v's lemmas of the same names (CmdRecCells.v: cmd_cf_cell, cmd_cf_got, cmd_cf_env, cmd_cf_grec,
   cmd_cf_lit); `AR_laws SEGS B` is the theorem AR_laws_ok, and cmd_val_objs is the statement's own premise. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandTac.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require check_words_add_c.
Module PCwa := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaRun PaShadow PaJournal CmdSyms CmdList CmdAddr CmdPa CmdPaLib CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaDenot PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_add_s1 check_words_add_s4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcmp).
Hypothesis ASTRNCMP : forall fx0 : YK11.FPState, @astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
(* the walk hypotheses CmdRecFacts' lemmas are closed over *)
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.

Theorem tcheck_words_add_proof : tcheck_words_add_spec B MT.
Proof.
unfold tcheck_words_add_spec.
(* Hcp8 (cp mod 8 = 0) and Hwp8 (wp mod 8 = 0) are the alignment premises the statement carries for the B build's
   UBSan alignment traps. The ASan build's code has no alignment trap (the walk meets none), and the walk's shadow
   checks of the call record and of w[3] / w[4] take the whole byte range (shent_ok_of_range), so the walk does not
   use them. *)
intros ly S W regs mem md cp wp r nargs p3 p4 q2 q3 w3 w4 x2 x3
H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 Hcp8 H12 H13 H14 H15 H16 H17 Hwp8 H18 H19 H20 H21.
exact (cwa_head B CMD_RLO CMD_RHI
(mkCwaFacts B (cmd_cf_cell B HB H9) (cmd_cf_got B HB H9)
  (cmd_cf_env SEGS B (AR_laws_ok SEGS B) HB IMG)
  (cmd_cf_grec SEGS B (AR_laws_ok SEGS B) HB) (cmd_cf_lit SEGS B (AR_laws_ok SEGS B) HB))
(* the walk runs at the one FP state fx (Section d), and cwa_head passes these to every strcmp / strncmp call *)
ly S W regs mem md cp wp r nargs p3 p4 q2 q3 w3 w4 x2 x3 (ASTRCMP fx) (ASTRNCMP fx)
H1 H2 H3 H4 H5 H6 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21).
Qed.

End e.
End f.
End d.
