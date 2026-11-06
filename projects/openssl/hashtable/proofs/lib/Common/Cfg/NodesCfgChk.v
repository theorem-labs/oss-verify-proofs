(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Section WithCfg.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.

Lemma chk_no_unmodeled : forall ms model x8 (chk : SyscallEffect -> check_result),
  (forall eff, check_syscall (sys_input segs ms x8) eff model = chk eff) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros ms model x8 chk Hchk Hnu Hs.
  pose proof (proj2 (check_syscall_err_iff (sys_input segs ms x8)
                       (mkEffect (Z_to_bv 64 0) [] []) model) Hs) as Hs'.
  rewrite Hchk in Hs'. exact (Hnu _ Hs').
Qed.

Lemma node_sys_chk_cfg_gen : forall ms model x8 (chk : SyscallEffect -> check_result) (J : Type)
    (E : J -> SyscallEffect) (M MM : J -> Model) (EV : J -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = chk eff) ->
  (forall j, chk (E j) = CheckOk (M j) (EV j)) ->
  (forall j, ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model (E j)) ->
  (forall j, m_halted (M j) = None) ->
  (forall j, materialize_model_accesses (M j) (syscall_effect_accesses (E j)) = Some (MM j)) ->
  (forall eff m' evs, chk eff = CheckOk m' evs ->
     (exists j, eff = E j /\ m' = M j /\ evs = EV j)
     \/ (m_halted m' = None
         /\ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff)) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  node_ok_cfg cfg segs (mkCfg ms model) J EV
    (fun j => mkCfg (advance_past_svc (apply_effect ms (E j))) (MM j)).
Proof.
  intros ms model x8 chk J E M MM EV Hh Hsvc Hchk Hok Hns Hnh Hmat Hinv Hnu.
  apply (node_sys_cfg_gen cfg segs ms model x8 J E M MM EV Hh Hsvc); try assumption.
  - intro j. apply check_syscall_ok_iff. rewrite Hchk. apply Hok.
  - intros eff m' evs Hs. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    exact (Hinv eff m' evs Hs).
  - eapply chk_no_unmodeled; eassumption.
Qed.

Lemma node_sys_chk_cfg_on : forall ms model x8 (chk : SyscallEffect -> check_result) (I : Type)
    (E : I -> SyscallEffect) (M MM : I -> Model) (EV : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  injected_family_off cfg (sys_input segs ms x8) = false ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = chk eff) ->
  (forall i, chk (E i) = CheckOk (M i) (EV i)) ->
  (forall eff m' evs, chk eff = CheckOk m' evs -> exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  (forall i, m_halted (M i) = None) ->
  (forall i, materialize_model_accesses (M i) (syscall_effect_accesses (E i)) = Some (MM i)) ->
  node_ok_cfg cfg segs (mkCfg ms model) I EV
    (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (MM i)).
Proof.
  intros ms model x8 chk I E M MM EV Hh Hsvc Hon Hchk Hok Hinv Hnu Hnh Hmat.
  apply (node_sys_chk_cfg_gen ms model x8 chk I E M MM EV Hh Hsvc Hchk Hok); try assumption.
  - intro i. apply spurious_refusal_family_on. exact Hon.
  - intros eff m' evs Hc. left. exact (Hinv eff m' evs Hc).
Qed.

Lemma node_sys_chk_cfg_nonrefusal : forall ms model x8 (chk : SyscallEffect -> check_result)
    (I : Type) (E : I -> SyscallEffect) (M MM : I -> Model) (EV : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (E i)) = false) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = chk eff) ->
  (forall i, chk (E i) = CheckOk (M i) (EV i)) ->
  (forall eff m' evs, chk eff = CheckOk m' evs -> exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  (forall i, m_halted (M i) = None) ->
  (forall i, materialize_model_accesses (M i) (syscall_effect_accesses (E i)) = Some (MM i)) ->
  node_ok_cfg cfg segs (mkCfg ms model) I EV
    (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (MM i)).
Proof.
  intros ms model x8 chk I E M MM EV Hh Hsvc Hnr Hchk Hok Hinv Hnu Hnh Hmat.
  apply (node_sys_chk_cfg_gen ms model x8 chk I E M MM EV Hh Hsvc Hchk Hok); try assumption.
  - intro i. apply spurious_refusal_not_refusal. apply Hnr.
  - intros eff m' evs Hc. left. exact (Hinv eff m' evs Hc).
Qed.

Lemma node_sys_chk_cfg_filter : forall ms model x8 (chk : SyscallEffect -> check_result)
    (J : Type) (E : J -> SyscallEffect) (M MM : J -> Model) (EV : J -> list event) (j0 : J),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  injected_family_off cfg (sys_input segs ms x8) = true ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = chk eff) ->
  (forall j, chk (E j) = CheckOk (M j) (EV j)) ->
  (forall j, refusal_b (sys_input segs ms x8) model (eff_ret (E j)) = false) ->
  (forall eff m' evs, chk eff = CheckOk m' evs ->
     m_halted m' = None
     /\ ((exists j, eff = E j /\ m' = M j /\ evs = EV j)
         \/ refusal_b (sys_input segs ms x8) model (eff_ret eff) = true)) ->
  (forall eff, chk eff <> CheckUnmodeled) ->
  (forall j, materialize_model_accesses (M j) (syscall_effect_accesses (E j)) = Some (MM j)) ->
  node_ok_cfg cfg segs (mkCfg ms model) J EV
    (fun j => mkCfg (advance_past_svc (apply_effect ms (E j))) (MM j)).
Proof.
  intros ms model x8 chk J E M MM EV j0 Hh Hsvc Hoff Hchk Hok Hnr Hinv Hnu Hmat.
  apply (node_sys_cfg_filter cfg segs ms model x8 J E M MM EV j0 Hh Hsvc Hoff); try assumption.
  - intro j. apply check_syscall_ok_iff. rewrite Hchk. apply Hok.
  - intros eff m' evs Hs. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    exact (Hinv eff m' evs Hs).
  - eapply chk_no_unmodeled; eassumption.
Qed.

(* [comment removed for export] *)
Lemma node_det_chk_cfg : forall ms model x8 eff0 m0 mm0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  materialize_model_accesses m0 (syscall_effect_accesses eff0) = Some mm0 ->
  node_ok_cfg cfg segs (mkCfg ms model) unit (fun _ => evs0)
    (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) mm0).
Proof.
  intros ms model x8 eff0 m0 mm0 evs0 Hh Hsvc Hchk Hnu Hh0 Hmat.
  apply (node_sys_chk_cfg_gen ms model x8
           (fun eff => check_syscall (sys_input segs ms x8) eff model) unit
           (fun _ => eff0) (fun _ => m0) (fun _ => mm0) (fun _ => evs0) Hh Hsvc).
  - intros eff. reflexivity.
  - intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
  - (* [comment removed for export] *)
    intros [] (_ & Hr & (eff' & m' & evs' & Hs & Hnr)).
    apply check_syscall_ok_iff in Hs. apply Hchk in Hs as (-> & _ & _).
    rewrite Hr in Hnr. discriminate Hnr.
  - intros []; exact Hh0.
  - intros []; exact Hmat.
  - intros eff m' evs Hc. left. apply Hchk in Hc as (-> & -> & ->). exists tt. auto.
  - exact Hnu.
Qed.

Lemma rzc_det_chk : forall ms model x8 eff0 m0 mm0 evs0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  materialize_model_accesses m0 (syscall_effect_accesses eff0) = Some mm0 ->
  realizes_cfg cfg segs (mkCfg (advance_past_svc (apply_effect ms eff0)) mm0) T ->
  realizes_cfg cfg segs (mkCfg ms model) (t_emit evs0 T).
Proof.
  intros ms model x8 eff0 m0 mm0 evs0 T Hh Hsvc Hchk Hnu Hh0 Hmat Hc.
  eapply rzc_emit1; [eapply node_det_chk_cfg; eassumption | exact Hc].
Qed.

Lemma rzc_det_chk_silent : forall ms model x8 eff0 m0 mm0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  materialize_model_accesses m0 (syscall_effect_accesses eff0) = Some mm0 ->
  realizes_cfg cfg segs (mkCfg (advance_past_svc (apply_effect ms eff0)) mm0) T ->
  realizes_cfg cfg segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 mm0 T Hh Hsvc Hchk Hnu Hh0 Hmat Hc.
  eapply rzc_silent1; [eapply node_det_chk_cfg; eassumption | exact Hc].
Qed.

End WithCfg.
