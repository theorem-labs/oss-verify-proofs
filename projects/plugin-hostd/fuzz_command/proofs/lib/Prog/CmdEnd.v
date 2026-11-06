From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL00 YL0g YL01 YI14 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI Img0 MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv RecInvP
  VerbsB Slot rec_calls_copy_c sup_chain_c sup_host_setting_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require rec_calls_copy SlotIter SlotItProof SlotItB3h.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CmdLink VerbsLink.
From OSSVerify.plugin_hostd.fuzz_command Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

(* The last link of plain_halts for LLVMFuzzerTestOneInput (plain): rec_calls_copy, then
   CmdLink.plain_halts_of_parts with VerbsLink.verbs_receive_of_given. The remaining premises are the pieces still
   being proved: one iteration of the slot loop and two recorder functions. *)

Lemma rec_calls_copy_of_given : forall B API LS SH SK ra empty, frame_given B API LS SH SK ra empty ->
  forall (rc : RunCeil) (fx : FPState), @rec_calls_copy_contract fx rc B (API rc).
Proof.
  intros B API LS SH SK ra empty FG rc fx. dep xstrdup_of_given FG rc fx. vl_setup FG B API rc fx.
  eapply lib.Prog.rec_calls_copy.rec_calls_copy_holds; eassumption.
Qed.

Section End.

Hypothesis ITER : SlotIter.iter_spec.

Theorem plain_halts_of_open : Statements.plain_halts.
Proof.
  exact (CmdLink.plain_halts_of_parts ITER VerbsLink.verbs_receive_of_given rec_calls_copy_of_given).
Qed.

End End.

(* One iteration of the slot loop: SlotItProof.iter_spec_holds with its (b2) step from SlotItB3h. *)
Theorem plain_halts_holds : Statements.plain_halts.
Proof. exact (plain_halts_of_open (SlotItProof.iter_spec_holds SlotItB3h.ib2_seg_h_closed)). Qed.
