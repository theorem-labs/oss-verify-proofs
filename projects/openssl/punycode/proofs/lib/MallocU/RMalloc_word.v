(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.openssl.punycode.lib.Malloc Require Import F_malloc_free MallocHINV MallocFacts_A Malloc_iface InitMem F_malloc_top Malloc_ifaceP.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.openssl.punycode.lib.MallocU Require Import RMallocRep RMallocTree RMallocKit_B RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.openssl.punycode.lib.Malloc Require MallocFacts_inv2.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Rnd.
From OSSVerify.Proofs.openssl.punycode.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
(* [comment removed for export] *)
Lemma RHEAP_block_word : forall s LB m p A n, RHEAP s LB m -> In (p, A, n) LB -> 0 < n -> wr_at usegs m A ((n - 1) / 8 * 8 + 8).
Proof.
  intros s LB m p A n HH HIN Hn.
  pose proof (RHEAP_block_range_proof s LB m (p, A, n) HH HIN) as (A0 & A16 & _).
  destruct HH as (st & LB0 & HP & _ & MR & [_ AR]). pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (IN0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact HIN]).
  destruct (rblock_inside st LB0 m (p, A, n) MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
  unfold blk_addr, blk_size in *. cbn [fst snd] in *.
  pose proof (rregion_addr_facts st m _ r MR Hr) as (_ & RAL & _).
  destruct MR as (_ & _ & _ & _ & _ & SH). destruct (SH _ r Hr Hk) as [(W0 & W1 & W) _].
  pose proof (MI_Cnt.round_up_pg_spec (r_len r)) as [_ RU].
  assert (HE : A + ((n - 1) / 8 * 8 + 8) <= r_base r + round_up_pg (r_len r)).
  { clear -A16 RAL RU HIB Hn. Z.div_mod_to_equations. lia. }
  split; [lia|]. split; [lia|]. intros i Hi.
  replace (A + i) with (r_base r + (A - r_base r + i)) by lia. apply W. lia.
Qed.
End WithCeiling0.
