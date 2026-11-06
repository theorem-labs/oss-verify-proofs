(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Arr SysStep Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma lb_bytes_cons : forall b LB, lb_bytes (b :: LB) = blk_size b + lb_bytes LB.
Proof. reflexivity. Qed.

Section HH.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Local Ltac hh := pose proof HH as (Ldone_mono_seq_lift & Lkrel & Lmpres & Lalloc & Lrf & Lbr & Lbd & Lnd & Laux & Llbr
                                     & Lmalloc & Lopnew & Lfree & Lopdel & Lopdel2 & Lnull1 & Lnull2).

  Lemma hh_done : forall (Q : config -> Prop) c, Q c -> hs_SR H Q c.
  Proof. hh. exact (proj1 Ldone_mono_seq_lift). Qed.
  Lemma hh_mono : forall (Q Q' : config -> Prop) c, hs_SR H Q c -> (forall c', Q c' -> Q' c') -> hs_SR H Q' c.
  Proof. hh. exact (proj1 (proj2 Ldone_mono_seq_lift)). Qed.
  Lemma hh_seq : forall (Q1 Q2 : config -> Prop) c, hs_SR H Q1 c -> (forall c', Q1 c' -> hs_SR H Q2 c') -> hs_SR H Q2 c.
  Proof. hh. exact (proj1 (proj2 (proj2 Ldone_mono_seq_lift))). Qed.
  Lemma hh_lift : forall (P : machine_state -> Prop) ms mo,
      m_halted mo = None -> m_vm_lazy mo = [] -> evt rsegs P ms ->
      hs_SR H (fun c => P (cfg_ms c) /\ cfg_model c = mo) (mkCfg ms mo).
  Proof. hh. exact (proj2 (proj2 (proj2 Ldone_mono_seq_lift))). Qed.
  Lemma hh_krel : forall s mo, hs_KREL H s mo -> m_halted mo = None /\ m_vm_lazy mo = [].
  Proof. hh. exact Lkrel. Qed.
  Lemma hh_mpres_refl : forall mo, hs_MPRES H mo mo.
  Proof. hh. exact (proj1 Lmpres). Qed.
  Lemma hh_mpres_trans : forall mo1 mo2 mo3, hs_MPRES H mo1 mo2 -> hs_MPRES H mo2 mo3 -> hs_MPRES H mo1 mo3.
  Proof. hh. exact (proj2 Lmpres). Qed.
  Lemma hh_alloc : alloc_ok_of_live H.
  Proof. hh. exact Lalloc. Qed.
  Lemma hh_RHEAP_frame : RHEAP_frame_stmt (hs_RHEAP H).
  Proof. hh. exact Lrf. Qed.
  Lemma hh_blocks : RHEAP_block_range_stmt (hs_RHEAP H).
  Proof. hh. exact Lbr. Qed.
  Lemma hh_disj : RHEAP_blocks_disjoint_stmt (hs_RHEAP H).
  Proof. hh. exact Lbd. Qed.
  Lemma hh_nodup : RHEAP_blocks_nodup_stmt (hs_RHEAP H).
  Proof. hh. exact Lnd. Qed.
  Lemma hh_rauxv_frame : rauxv_ok_frame_stmt (hs_rauxv_ok H).
  Proof. hh. exact Laux. Qed.
  Lemma hh_lb_remove : lb_remove_laws H.
  Proof. hh. exact Llbr. Qed.
  Lemma hh_malloc : malloc_sr_stmt H.
  Proof. hh. exact Lmalloc. Qed.
  Lemma hh_opnew : opnew_sr_stmt H.
  Proof. hh. exact Lopnew. Qed.
  Lemma hh_free : free_sr_stmt H.
  Proof. hh. exact Lfree. Qed.
  Lemma hh_opdel : opdel_sr_stmt H.
  Proof. hh. exact Lopdel. Qed.
  Lemma hh_opdel2 : opdel2_sr_stmt H.
  Proof. hh. exact Lopdel2. Qed.
  Lemma hh_opdel_null : opdel_null_sr_stmt_at H ROPDEL.
  Proof. hh. exact Lnull1. Qed.
  Lemma hh_opdel2_null : opdel_null_sr_stmt_at H ROPDEL2.
  Proof. hh. exact Lnull2. Qed.

  (* [comment removed for export] *)
  Lemma hh_evt : forall (P : machine_state -> Prop) (Q : config -> Prop) ms mo s,
    hs_KREL H s mo -> evt rsegs P ms -> (forall ms', P ms' -> Q (mkCfg ms' mo)) -> hs_SR H Q (mkCfg ms mo).
  Proof.
    intros P Q ms mo s K E W. destruct (hh_krel _ _ K) as [K1 K2].
    eapply hh_mono; [eapply hh_lift; [exact K1| exact K2| exact E]|].
    intros [ms' mo'] [HP E']. cbn in HP, E'. subst mo'. apply W. exact HP.
  Qed.

  (* [comment removed for export] *)
  Lemma hh_evt_then : forall (P : machine_state -> Prop) (Q : config -> Prop) ms mo s,
    hs_KREL H s mo -> evt rsegs P ms -> (forall ms', P ms' -> hs_SR H Q (mkCfg ms' mo)) -> hs_SR H Q (mkCfg ms mo).
  Proof.
    intros P Q ms mo s K E W. destruct (hh_krel _ _ K) as [K1 K2].
    eapply hh_seq; [eapply hh_lift; [exact K1| exact K2| exact E]|].
    intros [ms' mo'] [HP E']. cbn in HP, E'. subst mo'. apply W. exact HP.
  Qed.
End HH.

End HCW.

