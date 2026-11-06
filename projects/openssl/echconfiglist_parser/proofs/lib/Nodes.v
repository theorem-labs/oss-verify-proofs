(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg RelSpec SimInv ExitSim CatSim FileSim ShapeAlg.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.

(* [comment removed for export] *)
Lemma sstep_svc_inv_raw : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep segs (mkCfg ms model) e st ->
  (exists eff model' evs,
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
      /\ ((exists model'', m_halted model' = None /\ e = evs
             /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
             /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
          \/ (m_halted model' = None /\ e = []
              /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
              /\ st = SError)
          \/ (exists code, m_halted model' = Some code /\ m_killed model' = None
              /\ e = evs ++ [ExitEv code (m_fs model')]
              /\ st = SNext (mkCfg ms model'))
          \/ (exists sig, m_killed model' = Some sig
              /\ e = evs ++ [KillEv sig (m_fs model')]
              /\ st = SNext (mkCfg ms model'))))
  \/ (syscall_spec (sys_input segs ms x8) model Unmodeled /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    left. eexists. repeat split; eauto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. left. repeat split; auto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. right. left. eexists. repeat split; eauto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. right. right. eexists. repeat split; eauto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    right. repeat split; auto.
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_svc_inv : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs the_scfg (mkCfg ms model) e st ->
  (exists eff model' evs,
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
      /\ ((exists model'', m_halted model' = None /\ e = evs
             /\ ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff
             /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
             /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
          \/ (m_halted model' = None /\ e = []
              /\ ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff
              /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
              /\ st = SError)
          \/ (exists code, m_halted model' = Some code /\ m_killed model' = None
              /\ e = evs ++ [ExitEv code (m_fs model')]
              /\ st = SNext (mkCfg ms model'))
          \/ (exists sig, m_killed model' = Some sig
              /\ e = evs ++ [KillEv sig (m_fs model')]
              /\ st = SNext (mkCfg ms model'))))
  \/ (syscall_spec (sys_input segs ms x8) model Unmodeled /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    left. eexists. repeat split; eauto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. left. repeat split; auto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. right. left. eexists. repeat split; eauto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. right. right. eexists. repeat split; eauto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    right. repeat split; auto.
Qed.

(* [comment removed for export] *)
Lemma sstep_svc_inv : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  (forall eff model' evs, syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
     m_killed model' = None) ->
  sstep_cfg segs the_scfg (mkCfg ms model) e st ->
  (exists eff model' evs,
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
      /\ ((exists model'', m_halted model' = None /\ e = evs
             /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
             /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
          \/ (m_halted model' = None /\ e = []
              /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
              /\ st = SError)
          \/ (exists code, m_halted model' = Some code
              /\ e = evs ++ [ExitEv code (m_fs model')]
              /\ st = SNext (mkCfg ms model'))))
  \/ (syscall_spec (sys_input segs ms x8) model Unmodeled /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hnk Hss.
  destruct (sstep_cfg_svc_inv ms model x8 e st Hsvc Hss)
    as [(eff & model' & evs & Hc & [(m'' & Hh2 & He & _ & Hmat & Hst)
                                   | [(Hh2 & He & _ & Hmat & Hst)
                                   | [(code & Hh2 & _ & He & Hst)
                                   | (sig & Hk & _ & _)]]])
       | Hun].
  - left. eexists _, _, _. split; [exact Hc|]. left. exists m''. auto.
  - left. eexists _, _, _. split; [exact Hc|]. right; left. auto.
  - left. eexists _, _, _. split; [exact Hc|]. right; right. exists code. auto.
  - exfalso. rewrite (Hnk _ _ _ Hc) in Hk. discriminate Hk.
  - right. exact Hun.
Qed.

(* [comment removed for export] *)
Lemma sstep_of_spec : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
  ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  sstep_cfg segs the_scfg (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hns Hh' Hlazy.
  apply (sstep_cfg_syscall segs the_scfg ms model x8 eff m' m' evs Hh Hsvc Hc Hns Hh').
  apply materialize_model_accesses_no_lazy. exact Hlazy.
Qed.

(* [comment removed for export] *)
Lemma not_spurious_det : forall ms model x8 eff0 m0 evs0,
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok eff0 m0 evs0) ->
  ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff0.
Proof.
  intros ms model x8 eff0 m0 evs0 Hchk (_ & Hr & (eff' & m' & evs' & Hspec & Hnr)).
  apply Hchk in Hspec. apply Ok_inj in Hspec as (-> & -> & ->).
  rewrite Hr in Hnr. discriminate Hnr.
Qed.

Lemma not_spurious_all_refusals : forall ms model x8 eff,
  (forall eff' m' evs', syscall_spec (sys_input segs ms x8) model (Ok eff' m' evs') ->
     refusal_b (sys_input segs ms x8) model (eff_ret eff') = true) ->
  ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff.
Proof.
  intros ms model x8 eff Hall (_ & _ & (eff' & m' & evs' & Hspec & Hnr)).
  rewrite (Hall _ _ _ Hspec) in Hnr. discriminate Hnr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma node_chk_ev_cfg : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (effs i) (ms' i) (evs i))) ->
  (forall i, ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
     ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
     m_halted m' = None) ->
  (~ syscall_spec (sys_input segs ms x8) model Unmodeled) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hns Hinv Hnh Hnu Hlazy.
  assert (Hh' : forall i, m_halted (ms' i) = None) by (intros i; exact (Hnh _ _ _ (Hok i))).
  split.
  - intros i. apply (sstep_of_spec ms model x8); auto.
  - intros e st Hss.
    destruct (sstep_cfg_svc_inv ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hs & Hmat & ->)
                                     | [(Hh2 & -> & Hs & Hmat & ->)
                                     | [(code & Hh2 & _ & -> & ->)
                                     | (sig & Hk & -> & ->)]]])
         | (Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc Hs) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
      injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc Hs) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
    + exfalso. rewrite (Hnh _ _ _ Hc) in Hh2. discriminate Hh2.
    + exfalso. rewrite (m_killed_of_m_halted_none _ (Hnh _ _ _ Hc)) in Hk. discriminate Hk.
    + exfalso. exact (Hnu Hc).
Qed.

(* [comment removed for export] *)
Lemma node_chk_ev : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (effs i) (ms' i) (evs i))) ->
  (forall i, ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (~ syscall_spec (sys_input segs ms x8) model Unmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hns Hinv Hnu Hh' Hlazy.
  apply (node_chk_ev_cfg ms model x8 I effs ms' evs Hh Hsvc Hok Hns).
  - intros eff m' ev Hc _. exact (Hinv _ _ _ Hc).
  - intros eff m' ev Hc. destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). apply Hh'.
  - exact Hnu.
  - exact Hlazy.
Qed.

(* [comment removed for export] *)
Lemma node_chk : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (effs i) (ms' i) [])) ->
  (forall i, ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     exists i, eff = effs i /\ m' = ms' i /\ evs = []) ->
  (~ syscall_spec (sys_input segs ms x8) model Unmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' Hh Hsvc Hok Hns Hinv Hnu Hh' Hlazy.
  apply (node_chk_ev ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok Hns); auto.
Qed.

(* [comment removed for export] *)
Lemma node_family : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event)
    (R : outcome SyscallEffect -> Prop),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> R o) ->
  (forall i, R (Ok (effs i) (ms' i) (evs i))) ->
  (forall o, R o -> exists i, o = Ok (effs i) (ms' i) (evs i)) ->
  (forall i, ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model (effs i)) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs R Hh Hsvc HR Hin Hout Hns Hh' Hlazy.
  apply (node_chk_ev ms model x8 I effs ms' evs Hh Hsvc).
  - intros i. apply HR. apply Hin.
  - exact Hns.
  - intros eff m' ev Hc. apply HR in Hc. destruct (Hout _ Hc) as (i & Hi).
    apply Ok_inj in Hi as (-> & -> & ->). exists i. auto.
  - intros Hc. apply HR in Hc. destruct (Hout _ Hc) as (i & Hi). exact (Unmodeled_Ok _ _ _ Hi).
  - exact Hh'.
  - exact Hlazy.
Qed.

(* [comment removed for export] *)
Lemma node_family_on : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event)
    (R : outcome SyscallEffect -> Prop),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  injected_family_off the_scfg (sys_input segs ms x8) = false ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> R o) ->
  (forall i, R (Ok (effs i) (ms' i) (evs i))) ->
  (forall o, R o -> exists i, o = Ok (effs i) (ms' i) (evs i)) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs R Hh Hsvc Hon HR Hin Hout Hh' Hlazy.
  apply (node_family ms model x8 I effs ms' evs R Hh Hsvc HR Hin Hout); [|exact Hh'|exact Hlazy].
  intros i. apply spurious_refusal_family_on. exact Hon.
Qed.

(* [comment removed for export] *)
Lemma node_family_cfg : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event)
    (R : outcome SyscallEffect -> Prop),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> R o) ->
  (forall i, R (Ok (effs i) (ms' i) (evs i))) ->
  (forall i, ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model (effs i)) ->
  (forall eff m' ev, R (Ok eff m' ev) ->
     ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model eff ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff m' ev, R (Ok eff m' ev) -> m_halted m' = None) ->
  (~ R Unmodeled) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs R Hh Hsvc HR Hin Hns Hout Hnh Hnu Hlazy.
  apply (node_chk_ev_cfg ms model x8 I effs ms' evs Hh Hsvc).
  - intros i. apply HR. apply Hin.
  - exact Hns.
  - intros eff m' ev Hc Hs. apply HR in Hc. exact (Hout _ _ _ Hc Hs).
  - intros eff m' ev Hc. apply HR in Hc. exact (Hnh _ _ _ Hc).
  - intros Hc. apply HR in Hc. exact (Hnu Hc).
  - exact Hlazy.
Qed.

(* [comment removed for export] *)
Lemma node_det : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok eff0 m0 evs0) ->
  m_halted m0 = None ->
  m_vm_lazy m0 = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hh0 Hlazy0.
  apply (node_family ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0)
           (fun o => o = Ok eff0 m0 evs0) Hh Hsvc Hchk).
  - intros []. reflexivity.
  - intros o ->. exists tt. reflexivity.
  - intros []. eapply not_spurious_det. exact Hchk.
  - intros []; exact Hh0.
  - intros []; exact Hlazy0.
Qed.

(* [comment removed for export] *)
Lemma node_ret_only : forall ms model x8 r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok (mkEffect r [] []) m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 r m' evs Hh Hsvc Hchk Hh' Hlazy.
  rewrite <- (apply_effect_no_write ms r).
  apply (node_det ms model x8 (mkEffect r [] []) m' evs Hh Hsvc Hchk Hh' Hlazy).
Qed.

(* [comment removed for export] *)
Lemma node_ret_only_copyins : forall ms model x8 reads r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o
             <-> o = Ok (with_copyins reads (mkEffect r [] [])) m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 reads r m' evs Hh Hsvc Hchk Hh' Hlazy.
  rewrite <- (apply_effect_copyins_no_write ms r reads).
  apply (node_det ms model x8 (with_copyins reads (mkEffect r [] [])) m' evs Hh Hsvc Hchk Hh' Hlazy).
Qed.

Lemma rz_ret_only : forall ms model x8 r m' evs T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok (mkEffect r [] []) m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) (t_emit evs T).
Proof.
  intros ms model x8 r m' evs T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_emit1; [eapply node_ret_only; eassumption | exact Hc].
Qed.

Lemma rz_ret_only_copyins : forall ms model x8 reads r m' evs T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o
             <-> o = Ok (with_copyins reads (mkEffect r [] [])) m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) (t_emit evs T).
Proof.
  intros ms model x8 reads r m' evs T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_emit1; [eapply node_ret_only_copyins; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma rz_ret_only_silent : forall ms model x8 r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok (mkEffect r [] []) m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_silent1; [eapply node_ret_only; eassumption | exact Hc].
Qed.

Lemma rz_ret_only_copyins_silent : forall ms model x8 reads r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o
             <-> o = Ok (with_copyins reads (mkEffect r [] [])) m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_silent1; [eapply node_ret_only_copyins; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma rz_det : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok eff0 m0 []) ->
  m_halted m0 = None ->
  m_vm_lazy m0 = [] ->
  realizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hh0 Hlazy0 Hc.
  eapply rz_silent1; [eapply node_det; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma rz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  (forall i, realizes segs (nx i) (T i)) ->
  realizes segs c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hc.
  apply (rz_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
  - apply (rz_node segs c I (fun _ => []) nx T i0 Hnode Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (realizes_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

(* [comment removed for export] *)
Lemma rz_exit_chk : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  realizes segs (mkCfg ms model)
           (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof. intros. eapply rz_exit; eassumption. Qed.

(* [comment removed for export] *)
Definition open_I (model : Model) : Type := {e : Z | In e openat_errnos} + unit.

Definition open_nx (ms : machine_state) (model : Model) (mk : word -> Model)
  (i : open_I model) : config :=
  match i with
  | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
  | inr _ => mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                   (mk (alloc_fd (m_fds model)))
  end.

Lemma node_open : forall ms model x8 reads (mk : word -> Model),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  injected_family_off the_scfg (sys_input segs ms x8) = false ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> open_out reads model mk o) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = []) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  node_ok segs (mkCfg ms model) (open_I model) (fun _ => []) (open_nx ms model mk).
Proof.
  intros ms model x8 reads mk Hh Hlazy Hsvc Hon Hchk Hmk Hmklazy Hfree.
  pose (effs := fun i : open_I model => match i with
          | inl (exist _ e _) => with_copyins reads (mkEffect (errno_ret e) [] [])
          | inr _ => with_copyins reads (mkEffect (alloc_fd (m_fds model)) [] []) end).
  pose (ms' := fun i : open_I model => match i with
          | inl _ => model | inr _ => mk (alloc_fd (m_fds model)) end).
  assert (Enx : forall i, open_nx ms model mk i
                          = mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
  { intros [[e He] | []]; cbn [open_nx effs ms']; rewrite apply_effect_copyins_no_write; reflexivity. }
  split.
  - intros i. rewrite Enx.
    apply (proj1 (node_family_on ms model x8 (open_I model) effs ms' (fun _ => []) _ Hh Hsvc Hon Hchk
                    ltac:(intros [[e He] | []]; [left; exists e; auto | right; auto])
                    ltac:(intros o [(e & He & ->) | (Hlk & ->)];
                            [exists (inl (exist _ e He)) | exists (inr tt)]; reflexivity)
                    ltac:(intros [[e He] | []]; [exact Hh | apply Hmk])
                    ltac:(intros [[e He] | []]; [exact Hlazy | apply Hmklazy])) i).
  - intros e st Hss.
    destruct (proj2 (node_family_on ms model x8 (open_I model) effs ms' (fun _ => []) _ Hh Hsvc Hon Hchk
                    ltac:(intros [[er Her] | []]; [left; exists er; auto | right; auto])
                    ltac:(intros o [(er & Her & ->) | (Hlk & ->)];
                            [exists (inl (exist _ er Her)) | exists (inr tt)]; reflexivity)
                    ltac:(intros [[er Her] | []]; [exact Hh | apply Hmk])
                    ltac:(intros [[er Her] | []]; [exact Hlazy | apply Hmklazy])) e st Hss)
      as (i & -> & ->).
    exists i. rewrite Enx. split; reflexivity.
Qed.

Lemma rz_open : forall ms model x8 reads (mk : word -> Model) A B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  injected_family_off the_scfg (sys_input segs ms x8) = false ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> open_out reads model mk o) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = []) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e, In e openat_errnos ->
     realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                       (mk (alloc_fd (m_fds model)))) B ->
  realizes segs (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 reads mk A B Hh Hlazy Hsvc Hon Hchk Hmk Hmklazy Hfree HA HB.
  apply (rz_alt2 segs (mkCfg ms model) {e : Z | In e openat_errnos} unit
           (open_nx ms model mk) A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - eapply node_open; eassumption.
  - intros [e He]. cbn [open_nx]. apply HA. exact He.
  - intros []. cbn [open_nx]. exact HB.
Qed.

End WithSegs.
