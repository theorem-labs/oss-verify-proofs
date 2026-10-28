(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import F_malloc_free MallocHINV MallocFacts_A MallocBlocks Malloc_iface InitMem F_malloc_top Malloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMallocKit_B RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require MallocFacts_inv2.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgHXU Require Import HxuImage.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].

Lemma wview_outside_mrd (m : word -> option byte) (a : Z) :
  0 <= a < 2 ^ 64 -> (a < 0x10000 \/ 0x353000 <= a) -> wview bgusegs m (wa a) <> None -> exists b, mrd bgusegs m (wa a) = Some b.
Proof.
  intros Ha Hout Hw. unfold mrd. unfold wview in Hw. destruct (m (wa a)) as [b|]; [exists b; reflexivity|]. exfalso. apply Hw.
  rewrite wa_unsigned by lia. rewrite find_seg by lia.
  repeat match goal with |- context [if ?c then _ else _] => replace c with false by (symmetry; apply andb_false_iff; lia) end.
  reflexivity.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma RHEAP_block_mapped : forall s LB m b, RHEAP s LB m -> In b LB ->
  forall i, 0 <= i < blk_size b ->
    wview bgusegs m (wa (blk_addr b + i)) <> None /\ exists x, mrd bgusegs m (wa (blk_addr b + i)) = Some x.
Proof.
  intros s LB m b (st & LB0 & HP & _ & MR & [_ AR]) HIN i Hi. pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact HIN]).
  destruct (rblock_inside st LB0 m b MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
  pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH _ r Hr Hk) as [(W0 & W1 & Hw) _].
  assert (Hwv : wview bgusegs m (wa (blk_addr b + i)) <> None).
  { specialize (Hw (blk_addr b + i - r_base r) ltac:(lia)). replace (r_base r + (blk_addr b + i - r_base r)) with (blk_addr b + i) in Hw by lia. exact Hw. }
  split; [exact Hwv|]. apply wview_outside_mrd; [lia | lia | exact Hwv].
Qed.

End WithCeiling0.
