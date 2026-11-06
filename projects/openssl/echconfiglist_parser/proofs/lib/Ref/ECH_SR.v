(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Section Laws.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Lemma HH_SR : SR_laws H. Proof. exact (proj1 HH). Qed.
  Lemma HH_KREL : KREL_laws H. Proof. exact (proj1 (proj2 HH)). Qed.
  Lemma HH_MPRES : MPRES_laws H. Proof. exact (proj1 (proj2 (proj2 HH))). Qed.
  Lemma HH_alloc_ok : alloc_ok_of_live H. Proof. exact (proj1 (proj2 (proj2 (proj2 HH)))). Qed.
  Lemma HH_RHEAP_frame : RHEAP_frame H. Proof. unfold heap_sr_hyps in HH. tauto. Qed.
  Lemma HH_RHEAP_block_range : RHEAP_block_range H. Proof. unfold heap_sr_hyps in HH. tauto. Qed.
  Lemma HH_RHEAP_blocks_disjoint : RHEAP_blocks_disjoint H. Proof. unfold heap_sr_hyps in HH. tauto. Qed.
  Lemma HH_RHEAP_blocks_nodup : RHEAP_blocks_nodup H. Proof. unfold heap_sr_hyps in HH. tauto. Qed.
  Lemma HH_rauxv_frame : rauxv_frame H. Proof. unfold heap_sr_hyps in HH. tauto. Qed.
  Lemma HH_lb_remove : lb_remove_laws H. Proof. unfold heap_sr_hyps in HH. tauto. Qed.
  Lemma HH_malloc : malloc_sr_stmt H. Proof. unfold heap_sr_hyps in HH. tauto. Qed.
  Lemma HH_free : free_sr_stmt H. Proof. unfold heap_sr_hyps in HH. tauto. Qed.
  Lemma HH_free_null : free_null_sr_stmt H. Proof. unfold heap_sr_hyps in HH. tauto. Qed.

  Lemma sr_done : forall (Q : config -> Prop) c, Q c -> hs_SR H Q c.
  Proof. exact (proj1 HH_SR). Qed.
  Lemma sr_mono : forall (Q Q' : config -> Prop) c, hs_SR H Q c -> (forall c', Q c' -> Q' c') -> hs_SR H Q' c.
  Proof. exact (proj1 (proj2 HH_SR)). Qed.
  Lemma sr_seq : forall (Q1 Q2 : config -> Prop) c, hs_SR H Q1 c -> (forall c', Q1 c' -> hs_SR H Q2 c') -> hs_SR H Q2 c.
  Proof. exact (proj1 (proj2 (proj2 HH_SR))). Qed.
  Lemma sr_evt : forall (P : machine_state -> Prop) ms mo,
    m_halted mo = None -> m_vm_lazy mo = [] -> evt rsegs P ms ->
    hs_SR H (fun c => P (cfg_ms c) /\ cfg_model c = mo) (mkCfg ms mo).
  Proof. exact (proj2 (proj2 (proj2 HH_SR))). Qed.

  Lemma krel_halted : forall s mo, hs_KREL H s mo -> m_halted mo = None.
  Proof. intros s mo K. exact (proj1 (HH_KREL s mo K)). Qed.
  Lemma krel_lazy : forall s mo, hs_KREL H s mo -> m_vm_lazy mo = [].
  Proof. intros s mo K. exact (proj2 (HH_KREL s mo K)). Qed.

  (* [comment removed for export] *)
  Lemma sr_evt_k : forall (P : machine_state -> Prop) ms mo (Q : config -> Prop),
    m_halted mo = None -> m_vm_lazy mo = [] -> evt rsegs P ms ->
    (forall ms', P ms' -> hs_SR H Q (mkCfg ms' mo)) ->
    hs_SR H Q (mkCfg ms mo).
  Proof.
    intros P ms mo Q Hh Hl EV K. eapply sr_seq; [eapply sr_evt; eassumption|].
    intros [ms' mo'] [HP HM]. cbn in HP, HM. subst mo'. apply K. exact HP.
  Qed.

  Lemma sr_evt_krel : forall (P : machine_state -> Prop) ms mo s (Q : config -> Prop),
    hs_KREL H s mo -> evt rsegs P ms ->
    (forall ms', P ms' -> hs_SR H Q (mkCfg ms' mo)) ->
    hs_SR H Q (mkCfg ms mo).
  Proof. intros P ms mo s Q K EV C. eapply sr_evt_k; [eapply krel_halted; exact K| eapply krel_lazy; exact K| exact EV| exact C]. Qed.

  Lemma mpres_refl : forall mo, hs_MPRES H mo mo. Proof. exact (proj1 HH_MPRES). Qed.
  Lemma mpres_trans : forall mo1 mo2 mo3, hs_MPRES H mo1 mo2 -> hs_MPRES H mo2 mo3 -> hs_MPRES H mo1 mo3.
  Proof. exact (proj2 HH_MPRES). Qed.
End Laws.

(* [comment removed for export] *)
Lemma lb_bytes_cons : forall b LB, lb_bytes (b :: LB) = blk_size b + lb_bytes LB.
Proof. reflexivity. Qed.
Lemma lb_bytes_app : forall L1 L2, lb_bytes (L1 ++ L2) = lb_bytes L1 + lb_bytes L2.
Proof. induction L1 as [|b L1 IH]; intros L2; [reflexivity|]. cbn [app]. rewrite !lb_bytes_cons, IH. lia. Qed.
Lemma lb_bytes_nonneg : forall LB, Forall (fun b => 0 <= blk_size b) LB -> 0 <= lb_bytes LB.
Proof.
  induction LB as [|b LB IH]; intros F. { cbv. discriminate. }
  rewrite lb_bytes_cons. pose proof (Forall_inv F) as H1. cbn in H1. pose proof (IH (Forall_inv_tail F)). lia.
Qed.

Lemma lb_big_cons : forall b LB, lb_big (b :: LB) = big1 (blk_size b) + lb_big LB.
Proof. reflexivity. Qed.
Lemma lb_big_app : forall L1 L2, lb_big (L1 ++ L2) = lb_big L1 + lb_big L2.
Proof. induction L1 as [|b L1 IH]; intros L2; [reflexivity|]. cbn [app]. rewrite !lb_big_cons, IH. lia. Qed.
Lemma big1_range : forall n, 0 <= big1 n <= 1.
Proof. intros n. unfold big1. destruct (BIGB <? n); lia. Qed.
Lemma big1_small : forall n, n <= BIGB -> big1 n = 0.
Proof. intros n H. unfold big1. destruct (BIGB <? n) eqn:E; [apply Z.ltb_lt in E; lia| reflexivity]. Qed.
Lemma lb_big_nonneg : forall LB, 0 <= lb_big LB.
Proof. induction LB as [|b LB IH]; [cbv; discriminate|]. rewrite lb_big_cons. pose proof (big1_range (blk_size b)). lia. Qed.

End HCW.
