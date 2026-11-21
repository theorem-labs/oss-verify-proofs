(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Sys/Nodes.v's rz_ret_only_copyins_silent, rz_ret_only_copyins_silent_chk and rz_cases, over BudgetWit.Rzb.realizes; each takes the node's no-allocation-call fact as one more premise. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the two copy-in lemmas take the RomBase.sys_rob premise that Sys/Nodes.v's node_ret_only_copyins now takes, placed after the no-allocation-call fact; RomBase imported). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv ExitSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg Require Import RomBase.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import RelSpec CatSim FileSim ShapeX.
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BudgetWit Require Import Rzb ShapeXB.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma rz_ret_only_copyins_silent : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  sys_rob segs (mkCfg ms model) ->
  (forall o, syscall_spec (sys_input segs ms x8) model o
             <-> o = Ok (with_copyins reads (mkEffect r [] [])) m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hna Hrob Hchk Hh' Hlazy Hc.
  eapply rz_silent1;
    [ eapply node_ret_only_copyins; eassumption
    | exact (grant_free_no segs ms model x8 Hsvc Hna)
    | exact Hc ].
Qed.

#[using="Type"] Lemma rz_ret_only_copyins_silent_chk : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  sys_rob segs (mkCfg ms model) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hna Hrob Hchk Hh' Hlazy Hc.
  apply (rz_ret_only_copyins_silent ms model x8 reads r m' T Hh Hsvc Hna Hrob); [| exact Hh' | exact Hlazy | exact Hc].
  intros o. destruct o as [eff m'' evs|]; split.
  - intros Hs. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_copyins_ok_iff in Hs as (-> & -> & ->). reflexivity.
  - intros H. apply Ok_inj in H as (-> & -> & ->). apply check_syscall_ok_iff. rewrite Hchk.
    apply check_ret_only_copyins_refl.
  - intros Hs. exfalso. apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs. exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
  - intros H. exfalso. exact (Unmodeled_Ok _ _ _ H).
Qed.

#[using="Type"] Lemma rz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  grant_free segs c ->
  (forall i, realizes segs (nx i) (T i)) ->
  realizes segs c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hg Hc.
  apply (rz_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
  - apply (rz_node segs c I (fun _ => []) nx T i0 Hnode Hg Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

End WithSegs.
