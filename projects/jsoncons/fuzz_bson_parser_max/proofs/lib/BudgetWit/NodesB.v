(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Nodes.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed rz_ret_only_copyins_silent_b; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/BudgetWit/NodesB.v, lines 16, 124, 133-136. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import SimInv ExitSim CatSim FileSim ShapeAlg DivergeSim SpinAlg SpinAlgX.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import Nodes.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.BudgetWit Require Import SpinAlgB.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.Common.Cfg Require RomBase.

Open Scope bv_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Section WithSegs.
Variable segs : list Segment.
Context {bmK : BMode}.
Variable scfg : SpuriousCfg.
Lemma node_chk_ev_sp : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
       (exists i, eff = effs i /\ m' = ms' i /\ ev = evs i)
    \/ (spurious_refusal_cfg scfg (sys_input segs ms x8) model eff /\ m_halted m' = None)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs scfg (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hns Hinv Hnu Hh' Hlazy.
  apply (node_svc segs scfg ms model x8 I effs ms' evs Hh Hsvc).
  - intros i. apply check_syscall_ok_iff. apply Hok.
  - exact Hns.
  - intros eff m' ev Hspec. apply Hinv. apply check_syscall_ok_iff. exact Hspec.
  - intros Hum. apply (Hnu (mkEffect (Z_to_bv 64 0) [] [])). apply check_syscall_err_iff. exact Hum.
  - exact Hh'.
  - exact Hlazy.
Qed.
Lemma node_chk_ev : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  (forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
  node_ok segs scfg (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hlazy Hns.
  apply (node_chk_ev_sp ms model x8 I effs ms' evs Hh Hsvc Hok Hns); try assumption.
  intros eff m' ev Hc. left. exact (Hinv eff m' ev Hc).
Qed.
Lemma uniform_not_spurious : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event) (b : bool),
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = b) ->
  forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i).
Proof.
  intros ms model x8 I effs ms' evs b Hinv Hb i (Hoff & Hr & eff' & m' & ev' & Hspec & Hnr).
  apply check_syscall_ok_iff in Hspec.
  destruct (Hinv _ _ _ Hspec) as (j & -> & _ & _).
  rewrite Hb in Hr. rewrite Hb in Hnr. congruence.
Qed.
Lemma node_det : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  m_vm_lazy m0 = [] ->
  node_ok segs scfg (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hlazy0.
  assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
            exists i : unit, eff = (fun _ => eff0) i /\ m' = (fun _ => m0) i /\ ev = (fun _ => evs0) i).
  { intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto. }
  apply (node_chk_ev ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
  - intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
  - exact Hinv.
  - exact Hnu.
  - intros []; exact Hh0.
  - intros []; exact Hlazy0.
  - apply (uniform_not_spurious ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0)
             (refusal_b (sys_input segs ms x8) model (eff_ret eff0)) Hinv).
    intros []. reflexivity.
Qed.
Lemma node_ret_only_copyins : forall ms model x8 reads r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  node_ok segs scfg (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 reads r m' evs Hh Hsvc Hchk Hh' Hlazy.
  rewrite <- (apply_effect_copyins_no_write ms r reads).
  apply (node_det ms model x8 (with_copyins reads (mkEffect r [] [])) m' evs Hh Hsvc).
  - intros eff m'' evs'. rewrite Hchk. apply check_ret_only_copyins_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_copyins_no_unmodeled.
  - exact Hh'.
  - exact Hlazy.
Qed.
Lemma rz_ret_only_copyins_silent_b : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  RomBase.sys_rob segs (mkCfg ms model) ->   (* LPS 08b1429, as [Nodes.rz_ret_only_copyins_silent] *)
  ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  SpinAlgB.rzb segs scfg (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  SpinAlgB.rzb segs scfg (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hrob Hna Hchk Hh' Hlazy Hc.
  eapply SpinAlgB.rzb_silent1;
    [eapply node_ret_only_copyins; eassumption | exact Hrob
    | exact (SpinAlgB.nalloc_ok_sysno ms model x8 Hsvc Hna) | exact Hc].
Qed.
End WithSegs.
