(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of chain_words (0x8dfd4, 279 instructions) on the ASan build of
   plugin-hostd/fuzz_command, in cgif_file_fuzzer's walk style: tchain_words_spec (chain_words_c.v) is
   chain_words_exact (chain_words_exact.v), which the six segments (chain_words_s1.v .. chain_words_s6.v) and the
   transport of the caller's objects (chain_words_j.v) prove, assembled by chain_words_a.v, at statement passes 4
   and 5. The Section hypotheses are the statement's callee contracts and runtime rules in
   its forall-fx0 form (chain_words_c.v:84-93) and the per-binary record facts with cgif's names; the facts the walk
   names are CmdRecFacts lemmas over IMG (chain_words_exact.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaLibF CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import number_c sup_chain_c sup_resp_c chain_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import chain_words_d chain_words_exact.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's callee contracts and runtime rules (chain_words_c.v:84-93) *)
Hypothesis NUMBER : forall fx0 : YK11.FPState, @tnumber_spec fx0 rc SK PI B MT.
Hypothesis SUP_CHAIN : forall fx0 : YK11.FPState, @tsup_chain_spec fx0 rc SK PI B MT.
Hypothesis SUP_RESP : forall fx0 : YK11.FPState, @tsup_resp_spec fx0 rc SK PI B MT.
Hypothesis SM3 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 3.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SHF5 : forall fx0 : YK11.FPState, @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIGMA CS___asan_set_shadow_f5) 0xf5.
(* the per-binary record facts *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.
Theorem chain_words_proved : tchain_words_spec B MT.
Proof.
exact (chain_words_exact B MT NUMBER SUP_CHAIN SUP_RESP SM3 SMP ASF FFL SHF5 HB TL TLF ML MTL MTFL SIGP IMG).
Qed.
End e.
End f.
End d.
