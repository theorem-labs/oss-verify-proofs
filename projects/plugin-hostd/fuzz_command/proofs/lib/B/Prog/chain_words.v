(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of chain_words (0x8da84, 298 instructions) on the ASan+UBSan build
   of plugin-hostd/fuzz_command, in cgif_file_fuzzer's walk style: tchain_words_spec (lib/B/Prog/chain_words_c.v,
   statements a working branch f490061c104) from the six segments (chain_words_s1.v .. chain_words_s6.v), the
   transport of the caller's objects (chain_words_j.v) and the assembly (chain_words_a.v), over the interface
   chain_words_d.v. The B twin of lib/A/Prog/chain_words.v (A walk a working branch 5e2cdad423e);
   A's chain_words_exact.v is gone, because the B statement already states the returned block's size exactly
   (chain_words_c.v:159, n = |x| + 1).

   The Section hypotheses are the statement's callee contracts and runtime rules (chain_words_c.v:106-116) and
   the per-binary record facts with the names of a Theorem Labs lane's RULING-STMT.md section 1; the facts the walk names
   (cw_prog_unownedP, cw_ro_imgP, cw_ro_of_rodP) are CmdRecFacts lemmas over IMG. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00 YG0q.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaLibF PaFx CmdRecBase CmdRecRo CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import number_c sup_chain_c sup_resp_c chain_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import chain_words_d chain_words_a chain_words_j.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
chain_words_s1 chain_words_s2 chain_words_s3 chain_words_s4 chain_words_s5 chain_words_s6.
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
(* the statement's callee contracts and runtime rules (chain_words_c.v:106-116) *)
Hypothesis NUMBER : forall fx0 : YK11.FPState, @tnumber_spec fx0 rc SK PI B MT.
Hypothesis SUP_CHAIN : forall fx0 : YK11.FPState, @tsup_chain_spec fx0 rc SK PI B MT.
Hypothesis SUP_RESP : forall fx0 : YK11.FPState, @tsup_resp_spec fx0 rc SK PI B MT.
Hypothesis SM3 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 3.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SHF5 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIGMA CS___asan_set_shadow_f5) 0xf5.
(* the per-binary record facts (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* g_rec / record.spill / g_quitting are unowned image bytes (CmdRecImg.v) *)
Let PROG_UNOWNED : cw_prog_unownedP B := cmd_prog_unowned SEGS B LAWS HB IMG.
(* the caller's objects at every cut (chain_words_j.v), over the read-only range's image bounds and the
   arodata_okP-to-cmd_ro_ok bridge (CmdRecRo.v) *)
Let TRANSP : cw_transportP B MT :=
  cw_transport_ok B MT (relro_img SEGS B LAWS HB IMG) PROG_UNOWNED (cmd_ro_ok_of_aro SEGS B LAWS HB IMG).
Theorem chain_words_proved : tchain_words_spec B MT.
Proof.
unfold tchain_words_spec.
intros ly S W regs mem md ch tok ntok cb ncb ptrs tks R O HPRE HFRM HROD H10 HTOK64 H11 HTOK HTOKS HCB HCBO HN HNR
  HV HREC HREF HCALLS HRO HVOBJ HFR HNEV HLIVE HMOK.
pose (c := mkCWX ly S W regs mem md ch tok ntok cb ncb ptrs tks R O 0).
assert (HP : cw_pre B MT c) by (constructor; assumption).
exact (cw_run B MT
  (cw_S1 B MT TL TLF SM3 SMP ML MTL MTFL)
  (cw_S2 B MT NUMBER TL SIGP MTFL TRANSP)
  (cw_S3 B MT NUMBER TL MTFL SIGP TRANSP)
  (cw_S4 B MT SUP_CHAIN MTL SIGP HB PROG_UNOWNED TRANSP)
  (cw_S5 B MT SUP_RESP MTL SIGP TRANSP)
  (fun fx0 : YK11.FPState => cw_S6 (fx := fx0) B MT ML MTFL ASF FFL SHF5 PROG_UNOWNED)
  c HP HFRM).
Qed.
End e.
End f.
End d.
