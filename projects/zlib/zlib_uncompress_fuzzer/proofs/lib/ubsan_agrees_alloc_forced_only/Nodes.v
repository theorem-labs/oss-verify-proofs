(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import DispatchCompute.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import SimInv ExitSim CatSim FileSim ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.FO Require Import FOCore FOStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Definition halt_ev (m' : Model) (code : word) : event :=
  match m_killed m' with
  | Some sig => KillEv sig (m_fs m')
  | None => ExitEv code (m_fs m')
  end.

Section WithSegs.
Variable segs : list Segment.

Lemma sstep_svc_inv : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs alloc_forced_cfg (mkCfg ms model) e st ->
  (exists eff model' evs,
      check_syscall (sys_input segs ms x8) eff model = CheckOk model' evs
      /\ ((exists model'', m_halted model' = None /\ e = evs
             /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
             /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
          \/ (m_halted model' = None /\ e = []
              /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
              /\ st = SError)
          \/ (exists code, m_halted model' = Some code
              /\ e = evs ++ [halt_ev model' code]
              /\ st = SNext (mkCfg ms model'))))
  \/ (exists eff, check_syscall (sys_input segs ms x8) eff model = CheckUnmodeled
      /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hss. apply sstep_cfg_sub in Hss.
  inversion Hss; subst; try congruence.
  -
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + left. eexists. repeat split; eauto.
  -
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. left. repeat split; auto.
  -
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. right. eexists. repeat split; eauto.
      unfold halt_ev. match goal with Hk : m_killed _ = None |- _ => rewrite Hk end. reflexivity.
  -
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. right.
      match goal with Hk : m_killed ?mm = Some _ |- _ =>
        destruct (m_halted mm) as [code|] eqn:Hhc;
          [| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
        exists code; split; [reflexivity | split; [unfold halt_ev; rewrite Hk; reflexivity | reflexivity]]
      end.
  -
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    right. exists (mkEffect (Z_to_bv 64 0) [] []). split; [|split; reflexivity].
    apply check_syscall_err_iff. assumption.
Qed.

Lemma sstep_of_check : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model eff ->
  sstep_cfg segs alloc_forced_cfg (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hh' Hlazy Hns.
  apply (sstep_cfg_syscall_ns segs alloc_forced_cfg ms model x8 eff m' m' evs Hns Hh Hsvc).
  - apply check_syscall_ok_iff. exact Hc.
  - exact Hh'.
  - apply materialize_model_accesses_no_lazy. exact Hlazy.
Qed.

(** Tier-2b port: a syscall with a single checked outcome never has a spurious refusal (a spurious
    refusal needs a second, non-refusal outcome). *)
Lemma no_spurious_det : forall i model eff0 m0 evs0,
  (forall eff m' evs, check_syscall i eff model = CheckOk m' evs -> eff = eff0) ->
  check_syscall i eff0 model = CheckOk m0 evs0 ->
  ~ spurious_refusal_cfg alloc_forced_cfg i model eff0.
Proof.
  intros i model eff0 m0 evs0 Huniq _ (_ & Hr & (eff' & m' & evs' & Hs & Hnr)).
  apply check_syscall_ok_iff in Hs. rewrite (Huniq _ _ _ Hs) in Hnr. congruence.
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
  (forall i, ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model (effs i)) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hlazy Hns. split.
  - intros i. apply (sstep_of_check ms model x8); auto.
  - intros e st Hss.
    destruct (sstep_svc_inv ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
      injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite Hh' in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

Lemma node_chk : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
  (forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
     exists i, eff = effs i /\ m' = ms' i /\ evs = []) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  (forall i, ~ spurious_refusal_cfg alloc_forced_cfg (sys_input segs ms x8) model (effs i)) ->
  node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' Hh Hsvc Hok Hinv Hnu Hh' Hlazy Hns.
  apply (node_chk_ev ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok); auto.
Qed.

(** Tier-2b port: an allocation arm whose successors are its grants (non-refusals), with at least one
    grant [i0].  Its family is off at [alloc_forced_cfg], so beside the grant every refusal is spurious
    and the filtered step only grants; the converse only has to cover the non-refusal answers. *)
Lemma node_chk_w : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model) (i0 : I),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  injected_family_off alloc_forced_cfg (sys_input segs ms x8) = true ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false) ->
  (forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
     refusal_b (sys_input segs ms x8) model (eff_ret eff) = false ->
     exists i, eff = effs i /\ m' = ms' i /\ evs = []) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs -> m_halted m' = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs (mkCfg ms model) I (fun _ => [])
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' i0 Hh Hsvc Hoff Hok Hnr Hinv Hnu Hhalt Hlazy. split.
  - intros i. apply (sstep_of_check ms model x8); [exact Hh | exact Hsvc | exact (Hok i)
      | exact (Hhalt _ _ _ (Hok i)) | exact (Hlazy i) |].
    apply spurious_refusal_not_refusal. exact (Hnr i).
  - intros e st Hss.
    inversion Hss; subst; try congruence;
      match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hsvc in H; inversion H; subst end.
    + match goal with
      | Hs : syscall_spec ?si _ (Ok ?eff ?m1 ?ev), Hn : ~ spurious_refusal_cfg _ _ _ ?eff,
        Hm : materialize_model_accesses ?m1 _ = Some _ |- _ =>
          apply check_syscall_ok_iff in Hs;
          destruct (refusal_b si model (eff_ret eff)) eqn:Er;
          [ exfalso; apply Hn; split; [exact Hoff | split; [exact Er |]];
            exists (effs i0), (ms' i0), []; split; [apply check_syscall_ok_iff; exact (Hok i0) | exact (Hnr i0)]
          | destruct (Hinv _ _ _ Hs Er) as (i & -> & -> & ->);
            rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hm; injection Hm as <-;
            exists i; split; reflexivity ]
      end.
    + match goal with
      | Hs : syscall_spec ?si _ (Ok ?eff ?m1 ?ev), Hn : ~ spurious_refusal_cfg _ _ _ ?eff,
        Hm : materialize_model_accesses ?m1 _ = None |- _ =>
          apply check_syscall_ok_iff in Hs;
          destruct (refusal_b si model (eff_ret eff)) eqn:Er;
          [ exfalso; apply Hn; split; [exact Hoff | split; [exact Er |]];
            exists (effs i0), (ms' i0), []; split; [apply check_syscall_ok_iff; exact (Hok i0) | exact (Hnr i0)]
          | destruct (Hinv _ _ _ Hs Er) as (i & -> & -> & ->);
            rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hm; discriminate Hm ]
      end.
    + match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hc : m_halted ?m1 = Some _ |- _ =>
          apply check_syscall_ok_iff in Hs; rewrite (Hhalt _ _ _ Hs) in Hc; discriminate Hc
      end.
    + match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?ev), Hk : m_killed ?m1 = Some _ |- _ =>
          apply check_syscall_ok_iff in Hs;
          rewrite (m_killed_of_m_halted_none _ (Hhalt _ _ _ Hs)) in Hk; discriminate Hk
      end.
    + exfalso. apply (Hnu (mkEffect (Z_to_bv 64 0) [] [])). apply check_syscall_err_iff. assumption.
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
  node_ok segs (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hlazy0.
  apply (node_chk_ev ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
  - intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
  - intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto.
  - exact Hnu.
  - intros []; exact Hh0.
  - intros []; exact Hlazy0.
  - intros []. apply (no_spurious_det _ model eff0 m0 evs0).
    + intros eff m' evs Hc. apply Hchk in Hc as (-> & _ & _). reflexivity.
    + apply (proj2 (Hchk eff0 m0 evs0)). auto.
Qed.

Lemma node_ret_only : forall ms model x8 r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 r m' evs Hh Hsvc Hchk Hh' Hlazy.
  rewrite <- (apply_effect_no_write ms r).
  apply (node_det ms model x8 (mkEffect r [] []) m' evs Hh Hsvc).
  - intros eff m'' evs'. rewrite Hchk. apply check_ret_only_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_no_unmodeled.
  - exact Hh'.
  - exact Hlazy.
Qed.

Lemma node_ret_only_copyins : forall ms model x8 reads r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
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



Lemma rz_ret_only_silent : forall ms model x8 r m' T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' []) ->
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
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' []) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 reads r m' T Hh Hsvc Hchk Hh' Hlazy Hc.
  eapply rz_silent1; [eapply node_ret_only_copyins; eassumption | exact Hc].
Qed.

Lemma rz_det : forall ms model x8 eff0 m0 T,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = [])) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  m_vm_lazy m0 = [] ->
  realizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
  realizes segs (mkCfg ms model) T.
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hnu Hh0 Hlazy0 Hc.
  eapply rz_silent1; [eapply node_det; eassumption | exact Hc].
Qed.

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
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = []) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  injected_family_off alloc_forced_cfg (sys_input segs ms x8) = false ->
  node_ok segs (mkCfg ms model) (open_I model) (fun _ => []) (open_nx ms model mk).
Proof.
  intros ms model x8 reads mk Hh Hlazy Hsvc Hchk Hmk Hmklazy Hfree Hon. split.
  - intros [[e He] | []]; cbn [open_nx].
    + rewrite <- (apply_effect_copyins_no_write ms (errno_ret e) reads).
      apply (sstep_of_check ms model x8); [exact Hh | exact Hsvc | | exact Hh | exact Hlazy
        | apply spurious_refusal_family_on; exact Hon].
      rewrite Hchk. apply check_open_result_copyins_ok_iff. left. exists e. auto.
    + rewrite <- (apply_effect_copyins_no_write ms (alloc_fd (m_fds model)) reads).
      apply (sstep_of_check ms model x8); [exact Hh | exact Hsvc | | apply Hmk | apply Hmklazy
        | apply spurious_refusal_family_on; exact Hon].
      rewrite Hchk. apply check_open_result_copyins_ok_iff.
      right. exists (alloc_fd (m_fds model)). auto.
  - intros e st Hss.
    destruct (sstep_svc_inv ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. injection Hmat as <-.
        exists (inl (exist _ er Her)). cbn [open_nx].
        rewrite apply_effect_copyins_no_write. split; reflexivity.
      * subst fd. rewrite (materialize_model_accesses_no_lazy _ _ (Hmklazy _)) in Hmat.
        injection Hmat as <-.
        exists (inr tt). cbn [open_nx]. rewrite apply_effect_copyins_no_write. split; reflexivity.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. discriminate.
      * rewrite (materialize_model_accesses_no_lazy _ _ (Hmklazy _)) in Hmat. discriminate.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * congruence.
      * rewrite Hmk in Hh2. discriminate.
    + exfalso. rewrite Hchk in Hc. exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hc).
Qed.

Lemma rz_open : forall ms model x8 reads (mk : word -> Model) A B,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = []) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  injected_family_off alloc_forced_cfg (sys_input segs ms x8) = false ->
  (forall e, In e openat_errnos ->
     realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  realizes segs (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                       (mk (alloc_fd (m_fds model)))) B ->
  realizes segs (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 reads mk A B Hh Hlazy Hsvc Hchk Hmk Hmklazy Hfree Hon HA HB.
  apply (rz_alt2 segs (mkCfg ms model) {e : Z | In e openat_errnos} unit
           (open_nx ms model mk) A B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - eapply node_open; eassumption.
  - intros [e He]. cbn [open_nx]. apply HA. exact He.
  - intros []. cbn [open_nx]. exact HB.
Qed.

End WithSegs.
