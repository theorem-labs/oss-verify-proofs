(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of chain_words (0x8dfd4, 279 instructions) on the ASan build of
   plugin-hostd/fuzz_command, in cgif_file_fuzzer's walk style: tchain_words_spec (chain_words_c.v) is
   chain_words_exact (chain_words_exact.v), which the six segments (chain_words_s1.v .. chain_words_s6.v) and the
   transport of the caller's objects (chain_words_j.v) prove, assembled by chain_words_a.v, at statement passes 4
   and 5. The Section hypotheses are the statement's callee contracts and runtime rules in
   its forall-fx0 form (chain_words_c.v:84-93) and the per-binary record facts with cgif's names; the facts the walk
   names are CmdRecFacts lemmas over IMG (chain_words_exact.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words.v, with its module paths and module names changed; 28 of its 58 lines of code are new or changed and 28 lines of the source are left out. *)
(* The walk of pin_set_words on the ASan+UBSan build of plugin-hostd/fuzz_command (image B, fuzz_command.asan-ubsan,
   entry 0x8e17c, 113 instructions): the contract tpin_set_words_spec (lib/B/Prog/pin_set_words_c.v) from the four
   segments of the walk, the B twin of a Theorem Labs lane's A walk (lib/A/Prog/pin_set_words.v, a working branch):

     pin_set_words_h.v   entry .. MID   the arity test, strlen(line), tok[3] and the inlined strcmp(tok[3], "-")
     pin_set_words_m.v   MID .. JOIN    ntok = 4, or ntok = 5 with strncmp(tok[4], "verdict=", 8)
     pin_set_words_ta.v  JOIN .. K2     tok[1], tok[2] and the call of pins_set (the B kit's cl_callS_pgF)
     pin_set_words_tb.v  K2 .. ret      lv2_refusals_forget(NULL) when pins_set accepted; the epilogue

   over the interface lib/B/Prog/pin_set_words_s4.v. pins_set reaches the printf wrappers and returns at some FP
   state fx1: Tb is proved at every ambient FP state and taken at fx1 (from_K2 (fx := fx1)). The nine UBSan trap
   branches are decided by the segments' symbolic runs from the atom facts on tok and tok[4].

   Section hypotheses: the four the statement names (the two recorder callees' contracts and a Theorem Labs lane's two string
   entries, at every FP state), and the per-binary record facts of a Theorem Labs lane's RULING-STMT.md with their final names:
   TL, HB, IMG, MTL, SIGP (PinSetWordsClosed.v discharges TL, IMG and SIGP at the B instance). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import pins_set_c lv2_refusals_forget_c pin_set_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import pin_set_words_s4.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
pin_set_words_h pin_set_words_m pin_set_words_ta pin_set_words_tb.
Import ListNotations.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's Section hypotheses (pin_set_words_c.v:110-114) *)
Hypothesis PINS_SET : forall fx0 : YK11.FPState, @tpins_set_spec fx0 rc SK PI B MT.
Hypothesis LV2_REFUSALS_FORGET : forall fx0 : YK11.FPState, @tlv2_refusals_forget_spec fx0 rc SK PI B MT.
Hypothesis STRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strlen).
Hypothesis STRNCMP : forall fx0 : YK11.FPState, @RtString.astrncmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strncmp).
(* the per-binary record facts (a Theorem Labs lane's RULING-STMT.md sections 1-2) *)
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.

Theorem tpin_set_words_proof : tpin_set_words_spec B MT.
Proof.
unfold tpin_set_words_spec.
intros ly S W regs mem md ch line nl tok ntok cb ncb T ptrs tks R O
HPRE HFRM HROD H10 Hl64 H11 Ht64 H12 Hlb Hlo HlT HlN HOBJ HTOKS Hcb Hcbo Hntk Hntok Hverb
HREC Hdecl Hcalls HRO HVO Hfr HEV HLIVE HMO.
set (c := mkPSWX ly S W regs mem md ch line nl tok ntok cb ncb T ptrs tks R O).
assert (HP : psw_pre B MT c)
by exact (mkPswPre B MT c HPRE HROD H10 Hl64 H11 Ht64 H12 Hlb Hlo HlT HlN HOBJ HTOKS Hcb Hcbo Hntk Hntok Hverb
  HREC Hdecl Hcalls HRO HVO Hfr HEV HLIVE HMO).
pose proof (fun fx1 : YK11.FPState => psw_Tb (fx := fx1) B MT TL HB IMG MTL SIGP LV2_REFUSALS_FORGET c HP) as FK2.
pose proof (psw_Ta B MT HB IMG MTL SIGP PINS_SET c HP HFRM FK2) as FJ.
pose proof (psw_M B MT HB IMG MTL STRNCMP c HP FJ) as FM.
exact (psw_H B MT TL HB IMG MTL STRLEN c HP FM).
Qed.
End e.
End f.
End d.
