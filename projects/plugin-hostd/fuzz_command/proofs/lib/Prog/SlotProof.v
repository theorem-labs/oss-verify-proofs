From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL00 YL0g YL01 YI14 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI Img0 MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel HarnessProps Slot SlotCallees.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotInv SlotIter SlotEnd.
Import ListNotations.
Local Open Scope Z_scope.

(* The slot of LLVMFuzzerTestOneInput (plain 0x14048): the entry (SlotEnd.start_ok), the message loop (one
   iteration is SlotIter.iter_spec, the loop runs at most 32 times), and the end (SlotEnd.end_ok). *)

Lemma head_bound : forall {rc : RunCeil} B API S rg mem0 md0 L0 A0 p0 n0 m c,
  SlotIter.head_at (rc := rc) B API S rg mem0 md0 L0 A0 p0 n0 m c -> 0 <= m <= 31.
Proof.
  intros rc B API S rg mem0 md0 L0 A0 p0 n0 m c (fx & p & n & L & A & regs & mem & md & R & O & q & _ & HI).
  destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & _). exact Hm.
Qed.

Section Proof.
Hypothesis ITER : SlotIter.iter_spec.

Theorem fuzz_command_slot_holds :
  (forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty -> cmd_callees B API) ->
  harness_props -> fuzz_command_slot.
Proof.
  intros CC HP. unfold fuzz_command_slot.
  intros B API LS SH SK ra empty FG DBL rc fx j Hj.
  unfold lib_contract_g.
  intros L A regs mem md p n pl b K PRE GI GIMG RO TS FZ HK.
  pose proof (CC B API LS SH SK ra empty FG) as CCB.
  pose proof CCB as (SMC & CWC & CRTC & RCC & CRC & CAC & CREFC & SNC & MCC & SSC & SCC).
  assert (RCL : forall fx' : FPState, @rec_clear_c.rec_clear_contract fx' rc B (API rc)) by (intros fx'; exact (RCC rc fx')).
  pose proof FG as FG'. SlotEnd.fg_destruct FG'.
  assert (RG2 : spZ regs = spZ regs) by reflexivity.
  rewrite F27.
  eapply YM06.SR_realizes; [| intros c' Hc'; apply HK; apply Hc'].
  rewrite F0. rewrite F0 in RO.
  eapply YM06.SR_bind; [eapply SlotEnd.start_ok; eassumption |].
  intros c1 [FIN|[HD|EX]].
  - apply YM06.SR_ret. exact FIN.
  - eapply YM06.SR_bind.
    { refine (YM06.SR_loopZ rsegs Z (fun w => 32 - w)
               (fun w c => SlotIter.head_at B (API rc) (spZ regs) regs mem md L A p n w c)
               (SlotIter.exit_at B (API rc) (spZ regs) regs mem md L A) _ 0 c1 HD).
      intros w c Hw. pose proof (head_bound _ _ _ _ _ _ _ _ _ _ _ _ Hw) as Hb.
      eapply YM06.SR_mono; [eapply ITER; eassumption |].
      intros c' [EX'|HD']; [left; exact EX' | right].
      exists (w + 1). pose proof (head_bound _ _ _ _ _ _ _ _ _ _ _ _ HD') as Hb'. split; [lia | exact HD']. }
    intros c2 EX2. eapply SlotEnd.end_ok; eassumption.
  - eapply SlotEnd.end_ok; eassumption.
Qed.

End Proof.
