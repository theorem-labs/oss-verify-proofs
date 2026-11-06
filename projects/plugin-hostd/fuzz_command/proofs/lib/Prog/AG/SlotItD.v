(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module paths changed; 599 of its 833 lines of code are new or changed and 2508 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/RecStubU.v, with its module paths and module names changed; 444 of its 497 lines of code are new or changed and 780 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/SlotItCK.v; 330 of its 390 lines of code are new or changed and 437 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/SlotItB3qh.v, with its module paths and numbers changed; 526 of its 771 lines of code are new or changed and 145 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/AG/SlotItB3h.v, with its module paths and module names changed; 19 of its 54 lines of code are new or changed and 736 lines of the source are left out. *)
(* lib/Prog/SlotItD.v with the agreement room cap CAP_AG (lib/SlotAgree.v) for CAPMAX. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL0g YL01 YL00 YI14 YI16 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require KindBGlue BlocksNodup.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import AllocSI AllocGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP SlotSpec SlotGlue SlotRuns HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Import SlotCallees SlotIter SlotEnd SlotItBase SlotItSt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_c send_message_c CommandB VerbsB CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Import SlotItA SlotItC0 SlotItD0 SlotItE.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import check_refusal_c check_round_trip_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Import SlotItD1 SlotItD2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Slot SlotInv SlotRec.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecTail RecAnsB.
Import ListNotations.
Local Open Scope Z_scope.

(* Segment (d) of one iteration of the message loop of the entry function (plain 0x14048): from the state after
   check_words returned (stC, pc 0x142dc) through check_refusal (stCR, pc 0x142e4) and check_round_trip to the
   state after it returned (stD, pc 0x142f4); with segment (e) (SlotItE.ie_tail), to the next loop head or the
   exit. *)

Section D.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound).
Hypothesis FG : Slot.frame_given B API LS SH SK ra empty.
Hypothesis PRE : lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b.
Hypothesis RG2 : spZ rg = S.

Notation CF := (SlotInv.CF B (API rc) S rg mem0 md0 L0 A0).
Notation FB := (SlotInv.FB S).

Lemma seg_d : check_refusal_contract -> (forall fx : FPState, @check_round_trip_contract fx rc B (API rc)) ->
  forall m p n R0 c, stC B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0 c ->
  SR rsegs c (fun c' => exists kt kc ka text copy arr,
    stD B API S rg mem0 md0 L0 A0 p0 n0 pl m p n kt kc ka text copy arr c').
Proof.
  intros CRC CRTC m p n R0 c HC.
  eapply SR_bind; [eapply seg_d1; eassumption|].
  intros c1 HC1. eapply seg_d2; eassumption.
Qed.

Lemma seg_de : check_refusal_contract -> (forall fx : FPState, @check_round_trip_contract fx rc B (API rc)) ->
  forall m p n R0 c, stC B API S rg mem0 md0 L0 A0 p0 n0 pl m p n R0 c ->
  SR rsegs c (fun c' => exit_at B (API rc) S rg mem0 md0 L0 A0 c' \/
                        head_at B (API rc) S rg mem0 md0 L0 A0 p0 n0 (m + 1) c').
Proof.
  intros CRC CRTC m p n R0 c HC.
  eapply SR_bind; [exact (seg_d CRC CRTC m p n R0 c HC)|].
  intros c1 (kt & kc & ka & text & copy & arr & HD).
  eapply ie_tail; eassumption.
Qed.

End D.
