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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP
  SlotSpec SlotGlue SlotRuns HarnessProps SlotCallees SlotIter SlotEnd SlotItBase SlotItSt verbs_receive_c
  send_message_c CommandB VerbsB CommandModel SlotItA SlotItC0 SlotItD0 SlotItE
  check_refusal_c check_round_trip_c SlotItD1 SlotItD2.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Slot SlotInv SlotRec RecTail RecAnsB.
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
