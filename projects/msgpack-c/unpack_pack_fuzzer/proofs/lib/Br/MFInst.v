(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem ITree Nodes NodesM Decode DecodeM.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad MSafe Prog KLink KStep KOwn PgArith.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import MF_Phi MF_SiteC MF_Evol.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue NodeSound TreeBridge TreeBridgeN KRel MPath Room Grant MMeas MF MFSites MFSiteA.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma T2_A_i : T2_A_stmt PHI.            Proof. exact T2_A. Qed.
Lemma T2_Bm_i : T2_Bm_stmt PHI PHIB.     Proof. exact T2_Bm_sim. Qed.
Lemma T2_Bf_i : T2_Bf_stmt PHI PHIB.     Proof. exact T2_Bf_sim. Qed.
Lemma T2_C_i : T2_C_stmt PHI.            Proof. exact T2_C_sim. Qed.
Lemma T2_Cbig_i : T2_Cbig_stmt PHI.      Proof. exact T2_Cbig_sim. Qed.

Theorem MF_A_succ_i : MF_A_succ_stmt.    Proof. exact MF_A_succ. Qed.
Theorem MF_B_succ_i : MF_B_succ_stmt.    Proof. exact (MF_B_succ PHI PHIB T2_A_i T2_Bm_i T2_Bf_i T2_Cbig_i). Qed.
Theorem MF_A_must_i : MF_A_must_stmt.    Proof. exact MF_A_must. Qed.
Theorem MF_B_must_i : MF_B_must_stmt.    Proof. exact (MF_B_must PHI PHIB T2_A_i T2_Bm_i T2_Bf_i T2_Cbig_i). Qed.
Theorem MF_C_must_i : MF_C_must_stmt.    Proof. exact (MF_C_must PHI PHIB T2_A_i T2_Bm_i T2_Bf_i T2_C_i T2_Cbig_i). Qed.
Theorem MF_C_succ_i : MF_C_succ_stmt.    Proof. exact (MF_C_succ PHI PHIB T2_A_i T2_Bm_i T2_Bf_i T2_C_i T2_Cbig_i). Qed.
Theorem MF3_A_i : MF3_A_stmt.            Proof. exact MF3_A. Qed.
Theorem MF3_B_i : MF3_B_stmt.            Proof. exact (MF3_B PHI PHIB T2_A_i T2_Bm_i T2_Bf_i T2_Cbig_i). Qed.
Theorem MF3_C_i : MF3_C_stmt.            Proof. exact (MF3_C PHI PHIB T2_A_i T2_Bm_i T2_Bf_i T2_C_i T2_Cbig_i). Qed.

Lemma histR_PHI : forall k s p, histR k s p -> PHI (ps_m s).
Proof. exact (hist_PHI PHI PHIB T2_A_i T2_Bm_i T2_Bf_i). Qed.

Theorem MF3_F_i : MF3_F_stmt.
Proof.
  intros k s p A p' A' s1 mo1 j s2 mo2 LB Hh (L0 & L0' & Hc0 & Hcp) HK Hin Hin' Hmo Hroom Hj Hp.
  assert (HB : PHIB (ps_m s1)).
  { eapply T2_Bm_i; [exact (histR_PHI _ _ _ Hh) | exact Hc0 | apply bufsz_ge | | exact Hcp].
    eapply cpath_some_not_overflow. exact Hcp. }
  destruct (raw_free_measure p A (bufsz k) s1 LB mo1 tt s2 mo2 1 0 HK Hin Hmo) as (k' & E' & Hk & HE & MS); [| exact Hp |].
  - intros L zs Hc Hlive Hok.
    destruct (T2_F_sim (ps_m s1) L (fst p) HB Hc Hlive) as (a & len & K & E & Hlen & HKr). rewrite E in Hok |- *.
    apply okpath_vis in Hok as (ru & zs' & -> & Hru & Hok). cbn [answer_ok] in Hru.
    destruct (HKr ru Hru) as [cs' Ek]. rewrite Ek in Hok. apply okpath_ret in Hok. subst zs'.
    cbn [evs_of length esum esize]. rewrite Ek. cbn [evs_of length esum]. lia.
  - eapply room_step; [exact Hroom | exact Hj | exact MS | lia | lia].
Qed.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.NodesM OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.DecodeM.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Prelim OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.KInv.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.MSafe OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KLink OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KOwn OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.PgArith.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MF_Phi OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MF_SiteC OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MF_Evol.
Import F_syscalls.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.StateGlue OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.NodeSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.TreeBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.TreeBridgeN OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.KRel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MPath OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.Room OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.Grant OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MMeas.
Import MF.TwinB MFSites.TwinB MFSiteA.TwinB.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma T2_A_i : T2_A_stmt PHI.            Proof. exact T2_A. Qed.
Lemma T2_Bm_i : T2_Bm_stmt PHI PHIB.     Proof. exact T2_Bm_sim. Qed.
Lemma T2_Bf_i : T2_Bf_stmt PHI PHIB.     Proof. exact T2_Bf_sim. Qed.
Lemma T2_C_i : T2_C_stmt PHI.            Proof. exact T2_C_sim. Qed.
Lemma T2_Cbig_i : T2_Cbig_stmt PHI.      Proof. exact T2_Cbig_sim. Qed.

Theorem MF_A_succ_i : MF_A_succ_stmt.    Proof. exact MF_A_succ. Qed.
Theorem MF_B_succ_i : MF_B_succ_stmt.    Proof. exact (MF_B_succ PHI PHIB T2_A_i T2_Bm_i T2_Bf_i T2_Cbig_i). Qed.
Theorem MF_A_must_i : MF_A_must_stmt.    Proof. exact MF_A_must. Qed.
Theorem MF_B_must_i : MF_B_must_stmt.    Proof. exact (MF_B_must PHI PHIB T2_A_i T2_Bm_i T2_Bf_i T2_Cbig_i). Qed.
Theorem MF_C_must_i : MF_C_must_stmt.    Proof. exact (MF_C_must PHI PHIB T2_A_i T2_Bm_i T2_Bf_i T2_C_i T2_Cbig_i). Qed.
Theorem MF_C_succ_i : MF_C_succ_stmt.    Proof. exact (MF_C_succ PHI PHIB T2_A_i T2_Bm_i T2_Bf_i T2_C_i T2_Cbig_i). Qed.
Theorem MF3_A_i : MF3_A_stmt.            Proof. exact MF3_A. Qed.
Theorem MF3_B_i : MF3_B_stmt.            Proof. exact (MF3_B PHI PHIB T2_A_i T2_Bm_i T2_Bf_i T2_Cbig_i). Qed.
Theorem MF3_C_i : MF3_C_stmt.            Proof. exact (MF3_C PHI PHIB T2_A_i T2_Bm_i T2_Bf_i T2_C_i T2_Cbig_i). Qed.

Lemma histR_PHI : forall k s p, histR k s p -> PHI (ps_m s).
Proof. exact (hist_PHI PHI PHIB T2_A_i T2_Bm_i T2_Bf_i). Qed.

Theorem MF3_F_i : MF3_F_stmt.
Proof.
  intros k s p A p' A' s1 mo1 j s2 mo2 LB Hh (L0 & L0' & Hc0 & Hcp) HK Hin Hin' Hmo Hroom Hj Hp.
  assert (HB : PHIB (ps_m s1)).
  { eapply T2_Bm_i; [exact (histR_PHI _ _ _ Hh) | exact Hc0 | apply bufsz_ge | | exact Hcp].
    eapply cpath_some_not_overflow. exact Hcp. }
  destruct (raw_free_measure p A (bufsz k) s1 LB mo1 tt s2 mo2 1 0 HK Hin Hmo) as (k' & E' & Hk & HE & MS); [| exact Hp |].
  - intros L zs Hc Hlive Hok.
    destruct (T2_F_sim (ps_m s1) L (fst p) HB Hc Hlive) as (a & len & K & E & Hlen & HKr). rewrite E in Hok |- *.
    apply okpath_vis in Hok as (ru & zs' & -> & Hru & Hok). cbn [answer_ok] in Hru.
    destruct (HKr ru Hru) as [cs' Ek]. rewrite Ek in Hok. apply okpath_ret in Hok. subst zs'.
    cbn [evs_of length esum esize]. rewrite Ek. cbn [evs_of length esum]. lia.
  - eapply room_step; [exact Hroom | exact Hj | exact MS | lia | lia].
Qed.

End CEIL.
End TwinB.
