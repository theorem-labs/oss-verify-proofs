From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_identity Require Statements.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YM05 YO0d YO09 YL0g.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import AgreeFrame AgreeZlib SlotAgree AllocSlots.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require AgreeZlib SlotAgree ZAllocator.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Agree.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require UAgree.
Import ListNotations.
Open Scope Z_scope.

Lemma room_calls_ag_u : forall n k, @room_calls checksum_shape_ag n k U.AgreeZlib.SBD_AG.
Proof.
  intros n k. pose proof CAP_AG_range as HC. pose proof UAgree.cap_ag_same as HE.
  induction k as [|k IH]; cbn [room_calls]; [exact I|].
  split; [|exact IH]. cbn. unfold U.AgreeZlib.SBD_AG. cbn [sb_live sb_bytes sb_cap]. lia.
Qed.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof.
  apply (ubsan_agrees_of_slots checksum_shape_ag [] (fun _ _ => True) [] (fun _ _ => True)).
  - intros a (lo & len & Hin & _). destruct Hin.
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - exact plain_slot_ag.
  - intros data. exact (room_calls_ag_u _ _).
  - intros a (lo & len & Hin & _). destruct Hin.
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj. exact (UAgree.ubsan_slot_cg rc fx j Hj).
Qed.
