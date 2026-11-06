(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of check_reply_answer (plugin-hostd/fuzz_command, 0x88450, 75 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close, a caller with calls). *)
(* Modified by Theorem Labs, 2026-10: re-walked on fuzz_command.asan-ubsan (0x88754, 81 instructions) from lib/A/Prog/check_reply_answer.v (a working branch 7308930bf5f): module paths, the image's addresses, the three UBSan trap sites (0x887c8, 0x88804, 0x8880c) decided by the run from atom facts, the strcmp test's branch sense (bnez to the abort block), and the record facts from lib/B/Prog/CmdRecFacts.v (a working branch 713692f1e0c): the literals' shadow by cmd_aread_ok_chk over CmdChk's checkers, their tails by cmd_tail_vis_at over CmdRo's cmd_ro_ends. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/check_reply_answer.v, with its module paths and module names changed; 29 of its 64 lines of code are new or changed and 581 lines of the source are left out. *)
(* check_words_add on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan): the proof of
   tcheck_words_add_spec B MT (lib/B/Prog/check_words_add_c.v). The B twin of lib/A/Prog/check_words_add.v
   (a working branch 1aea12cabb8). The walk is in check_words_add_s4.v (entry 0x88eac .. 0x88f64),
   check_words_add_s2.v / _s3.v (0x88f64 .. 0x88fe8, the literal and the word placement) and
   check_words_add_s2.v (0x88fe8 .. ret); the run decides the 11 UBSan trap sites not taken from atom facts
   (the statement's address ranges, its `cp mod 8 = 0` and `wp mod 8 = 0`).

   Section hypotheses: the two wrapper contracts the statement names (ASTRCMP, ASTRNCMP, fx-generic since
   a working branch 713692f1e0c, applied at fx) and RULING-STMT §1's walk
   hypotheses `HB : CmdBSyms B` (lib/B/YF0m.v:4875) and `IMG : cmd_img_facts SEGS B` (lib/B/Prog/CmdRecBase.v:339;
   this walk calls runtime entries). check_words_add_s1.v's record CwaFacts is built by exact from a Theorem Labs lane's shared
   record lemmas (lib/B/Prog/CmdRecFacts.v, a working branch 6830f0bf032): cf_cell / cf_got from CmdRecCells'
   cmd_cf_cell / cmd_cf_got (with the statement's cmd_val_objs), cf_env from cmd_cf_env, cf_grec from cmd_cf_grec,
   cf_lit from cmd_cf_lit, cf_tail from CmdRecRest's cmd_tail_vis. `AR_laws SEGS B` is the theorem AR_laws_ok
   (check_words_add_s1.v's cwa_laws), not a hypothesis. lib/B/Prog/CheckWordsAddClosed.v discharges IMG at the
   pinned image (CmdRecImg.cmd_img_facts_tfib). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandTac.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require check_words_add_c.
Module PCwa := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.check_words_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaRun PaShadow PaJournal CmdSyms CmdList CmdAddr CmdPa CmdPaLib CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall PaCallRun PaDenot PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_add_s1 check_words_add_s4.
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
(* the runtime entries, at every FP state (check_words_add_c.v:77-78); the walk applies them at fx *)
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strcmp).
Hypothesis ASTRNCMP : forall fx0 : YK11.FPState, @astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
(* the allocator record of fuzz_command.asan-ubsan (lib/B/YF0m.v; the instance's CmdB_syms, lib/B/YD2l.v) *)
Hypothesis HB : CmdBSyms B.
(* the image's facts (lib/B/Prog/CmdRecBase.v:339; cmd_img_facts_tfib for the instance) *)
Hypothesis IMG : cmd_img_facts SEGS B.

Theorem tcheck_words_add_proof : tcheck_words_add_spec B MT.
Proof.
unfold tcheck_words_add_spec.
intros ly S W regs mem md cp wp r nargs p3 p4 q2 q3 w3 w4 x2 x3
H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23.
exact (cwa_head B CMD_RLO CMD_RHI
(mkCwaFacts B (cmd_cf_cell B HB H9) (cmd_cf_got B HB H9) (cmd_cf_env SEGS B (cwa_laws B) HB IMG)
  (cmd_cf_grec SEGS B (cwa_laws B) HB) (cmd_cf_lit SEGS B (cwa_laws B) HB) (cmd_tail_vis SEGS B (cwa_laws B) HB))
ly S W regs mem md cp wp r nargs p3 p4 q2 q3 w3 w4 x2 x3 (ASTRCMP fx) (ASTRNCMP fx)
H1 H2 H3 H4 H5 H6 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23).
Qed.

End e.
End f.
End d.
