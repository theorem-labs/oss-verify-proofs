From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL0g YL01 YI14 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI Img0 MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import Slot SlotCallees.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecModel HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require SlotInv SlotIter SlotEnd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

(* The slot of LLVMFuzzerTestOneInput (ubsan 0x14060): the entry (CF.SlotEnd.start_ok), the message loop (one
   iteration is CF.SlotIter.iter_spec, the loop runs at most 32 times), and the end (CF.SlotEnd.end_ok). *)

Lemma head_bound : forall {rc : RunCeil} B API S rg mem0 md0 L0 A0 p0 n0 m c,
  CF.SlotIter.head_at (rc := rc) B API S rg mem0 md0 L0 A0 p0 n0 m c -> 0 <= m <= 31.
Proof.
  intros rc B API S rg mem0 md0 L0 A0 p0 n0 m c (fx & p & n & L & A & regs & mem & md & R & O & q & _ & HI).
  destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hm & _). exact Hm.
Qed.

Section Proof.
Hypothesis ITER : CF.SlotIter.iter_spec.

Theorem fuzz_command_slot_holds :
  (forall B API LS SH SK ra empty, CF.Slot.frame_given_u B API LS SH SK ra empty -> CF.SlotCallees.cmd_callees B API) ->
  HarnessProps.harness_props -> CF.Slot.fuzz_command_slot_u.
Proof.
  intros CC HP. unfold fuzz_command_slot_u.
  intros B API LS SH SK ra empty FG DBL rc fx j Hj.
  unfold lib_contract_cg.
  intros L A regs mem md p n pl b K PRE GI GIMG RO TS FZ HK.
  pose proof (CC B API LS SH SK ra empty FG) as CCB.
  pose proof CCB as (SMC & CWC & CRTC & RCC & CRC & CAC & CREFC & SNC & MCC & SSC & SCC).
  assert (RCL : forall fx' : FPState, @CF.rec_clear_c.rec_clear_contract fx' rc B (API rc))
    by (intros fx'; exact (RCC rc fx')).
  pose proof FG as FG'. CF.SlotEnd.fg_destruct FG'.
  assert (RG2 : spZ regs = spZ regs) by reflexivity.
  rewrite F27.
  eapply (SR_realizes_ms B (ms_segs B) eq_refl); [| intros c' Hc'; apply HK; apply Hc'].
  rewrite F0. rewrite F0 in RO.
  eapply SR_bind; [eapply CF.SlotEnd.start_ok; eassumption |].
  intros c1 [FIN|[HD|EX]].
  - apply SR_ret. exact FIN.
  - eapply SR_bind.
    { refine (SR_loopZ rsegs Z (fun w => 32 - w)
               (fun w c => CF.SlotIter.head_at B (API rc) (spZ regs) regs mem md L A p n w c)
               (CF.SlotIter.exit_at B (API rc) (spZ regs) regs mem md L A) _ 0 c1 HD).
      intros w c Hw. pose proof (head_bound _ _ _ _ _ _ _ _ _ _ _ _ Hw) as Hb.
      eapply SR_mono; [eapply ITER; eassumption |].
      intros c' [EX'|HD']; [left; exact EX' | right].
      exists (w + 1). pose proof (head_bound _ _ _ _ _ _ _ _ _ _ _ _ HD') as Hb'. split; [lia | exact HD']. }
    intros c2 EX2. eapply CF.SlotEnd.end_ok; eassumption.
  - eapply CF.SlotEnd.end_ok; eassumption.
Qed.

End Proof.
