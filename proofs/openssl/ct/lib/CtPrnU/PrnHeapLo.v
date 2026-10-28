(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import F_malloc_free MallocHINV MallocFacts_A Malloc_iface InitMem F_malloc_top Malloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMallocKit_B RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require MallocFacts_inv2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma RHEAP_block_ge_4096 : forall s LB m b, RHEAP s LB m -> In b LB -> 4096 <= blk_addr b.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros s LB m b (st & LB0 & HP & _ & MR & [_ AR]) HIN. pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact HIN]).
  destruct (rblock_inside st LB0 m b MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1). lia.
Qed.

Lemma RHEAP_In_ge_4096 : forall s LB m p A n, RHEAP s LB m -> In (p, A, n) LB -> 4096 <= A.
Proof. intros s LB m p A n H HIn. exact (RHEAP_block_ge_4096 s LB m (p, A, n) H HIn). Qed.
End WithCeiling0.
