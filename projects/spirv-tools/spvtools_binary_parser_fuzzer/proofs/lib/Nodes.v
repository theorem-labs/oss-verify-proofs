(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Classical IndefiniteDescription.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RelSpec SimInv ExitSim CatSim FileSim ShapeAlg.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Ltac nonalloc_tac :=
  first
  [ reflexivity
  | match goal with
    | |- alloc_sysno_b (bv_unsigned ?x) = false =>
        match goal with
        | H : x = _ |- _ => rewrite H; reflexivity
        | H : bv_unsigned x = _ |- _ => rewrite H; reflexivity
        end
    end ].

Section WithSegs.
Variable segs : list Segment.

Lemma sstep_svc_inv : forall ms model x8 e st,
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
          \/ (exists code, m_halted model' = Some code
              /\ e = evs ++ [halt_ev model' code]
              /\ st = SNext (mkCfg ms model'))))
  \/ (syscall_spec (sys_input segs ms x8) model Unmodeled /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hss.
  inversion Hss; subst; try congruence.
  -
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    left. eexists. repeat split; eauto.
  -
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. left. repeat split; auto.
  -
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. right. eexists. repeat split; eauto.
    rewrite halt_ev_exit by assumption. reflexivity.
  -
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split; [eassumption|].
    right. right.
    match goal with Hk : m_killed ?mm = Some ?s |- _ =>
      exists s; split; [exact (m_halted_of_killed _ _ Hk) |];
      split; [rewrite (halt_ev_killed _ _ Hk); reflexivity | reflexivity]
    end.
  -

    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    right. repeat split; auto.
Qed.

Lemma sstep_of_spec : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  sstep segs (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hh' Hlazy.
  apply (sstep_syscall segs ms model x8 eff m' m' evs Hh Hsvc Hc Hh').
  apply materialize_model_accesses_no_lazy. exact Hlazy.
Qed.

Lemma node_chk_ev : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  alloc_sysno_b (bv_unsigned x8) = false ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (effs i) (ms' i) (evs i))) ->
  (forall eff m' ev, syscall_spec (sys_input segs ms x8) model (Ok eff m' ev) ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (~ syscall_spec (sys_input segs ms x8) model Unmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hna Hok Hinv Hnu Hh' Hlazy.
  apply (node_ok_lift_sys segs ms model x8); [exact Hsvc | exact Hna |]. split.
  - intros i. apply (sstep_of_spec ms model x8); auto.
  - intros e st Hss.
    destruct (sstep_svc_inv ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
      injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite Hh' in Hh2. discriminate.
    + exfalso. exact (Hnu Hc).
Qed.

Lemma node_family : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event)
    (R : outcome SyscallEffect -> Prop),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  alloc_sysno_b (bv_unsigned x8) = false ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> R o) ->
  (forall i, R (Ok (effs i) (ms' i) (evs i))) ->
  (forall o, R o -> exists i, o = Ok (effs i) (ms' i) (evs i)) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs R Hh Hsvc Hna HR Hin Hout Hh' Hlazy.
  apply (node_chk_ev ms model x8 I effs ms' evs Hh Hsvc Hna).
  - intros i. apply HR. apply Hin.
  - intros eff m' ev Hc. apply HR in Hc. destruct (Hout _ Hc) as (i & Hi).
    apply Ok_inj in Hi as (-> & -> & ->). exists i. auto.
  - intros Hc. apply HR in Hc. destruct (Hout _ Hc) as (i & Hi). exact (Unmodeled_Ok _ _ _ Hi).
  - exact Hh'.
  - exact Hlazy.
Qed.

Lemma node_det : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  alloc_sysno_b (bv_unsigned x8) = false ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok eff0 m0 evs0) ->
  m_halted m0 = None ->
  m_vm_lazy m0 = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hna Hchk Hh0 Hlazy0.
  apply (node_family ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0)
           (fun o => o = Ok eff0 m0 evs0) Hh Hsvc Hna Hchk).
  - intros []. reflexivity.
  - intros o ->. exists tt. reflexivity.
  - intros []; exact Hh0.
  - intros []; exact Hlazy0.
Qed.

Lemma node_ret_only : forall ms model x8 r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  alloc_sysno_b (bv_unsigned x8) = false ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok (mkEffect r [] []) m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 r m' evs Hh Hsvc Hna Hchk Hh' Hlazy.
  rewrite <- (apply_effect_no_write ms r).
  apply (node_det ms model x8 (mkEffect r [] []) m' evs Hh Hsvc Hna Hchk Hh' Hlazy).
Qed.

Lemma node_ret_only_copyins : forall ms model x8 reads r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  alloc_sysno_b (bv_unsigned x8) = false ->
  (forall o, syscall_spec (sys_input segs ms x8) model o
             <-> o = Ok (with_copyins reads (mkEffect r [] [])) m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 reads r m' evs Hh Hsvc Hna Hchk Hh' Hlazy.
  rewrite <- (apply_effect_copyins_no_write ms r reads).
  apply (node_det ms model x8 (with_copyins reads (mkEffect r [] [])) m' evs Hh Hsvc Hna Hchk Hh' Hlazy).
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
  alloc_sysno_b (bv_unsigned x8) = false ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> open_out reads model mk o) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = []) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  node_ok segs (mkCfg ms model) (open_I model) (fun _ => []) (open_nx ms model mk).
Proof.
  intros ms model x8 reads mk Hh Hlazy Hsvc Hna Hchk Hmk Hmklazy Hfree.
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
    apply (proj1 (node_family ms model x8 (open_I model) effs ms' (fun _ => []) _ Hh Hsvc Hna Hchk
                    ltac:(intros [[e He] | []]; [left; exists e; auto | right; auto])
                    ltac:(intros o [(e & He & ->) | (Hlk & ->)];
                            [exists (inl (exist _ e He)) | exists (inr tt)]; reflexivity)
                    ltac:(intros [[e He] | []]; [exact Hh | apply Hmk])
                    ltac:(intros [[e He] | []]; [exact Hlazy | apply Hmklazy])) i).
  - intros e st Hss.
    destruct (proj2 (node_family ms model x8 (open_I model) effs ms' (fun _ => []) _ Hh Hsvc Hna Hchk
                    ltac:(intros [[er Her] | []]; [left; exists er; auto | right; auto])
                    ltac:(intros o [(er & Her & ->) | (Hlk & ->)];
                            [exists (inl (exist _ er Her)) | exists (inr tt)]; reflexivity)
                    ltac:(intros [[er Her] | []]; [exact Hh | apply Hmk])
                    ltac:(intros [[er Her] | []]; [exact Hlazy | apply Hmklazy])) e st Hss)
      as (i & -> & ->).
    exists i. rewrite Enx. split; reflexivity.
Qed.

Lemma node_family_cfg : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event)
    (R : outcome SyscallEffect -> Prop),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> R o) ->
  (forall i, R (Ok (effs i) (ms' i) (evs i))) ->
  (forall o, R o -> exists i, o = Ok (effs i) (ms' i) (evs i)) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs (mkCfg ms model)
    {i : I | ~ spurious_refusal_cfg CFG (sys_input segs ms x8) model (effs i)}
    (fun j => evs (proj1_sig j))
    (fun j => mkCfg (advance_past_svc (apply_effect ms (effs (proj1_sig j)))) (ms' (proj1_sig j))).
Proof.
  intros ms model x8 I effs ms' evs R Hh Hsvc HR Hin Hout Hh' Hlazy. split.
  - intros [i Hi]. cbn [proj1_sig].
    apply (sstep_cfg_syscall segs CFG ms model x8 (effs i) (ms' i) (ms' i) (evs i));
      [exact Hh | exact Hsvc | apply HR; apply Hin | exact Hi | apply Hh'
      | apply materialize_model_accesses_no_lazy; apply Hlazy].
  - intros e st Hss.
    destruct (sstep_cfg_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & m' & ev & Hc & Hcase) | (Hc & _ & _)].
    + apply HR in Hc. destruct (Hout _ Hc) as (i & Hi). apply Ok_inj in Hi as (-> & -> & ->).
      destruct Hcase as [(m'' & Hns & _ & -> & Hmat & ->) | [(Hns & _ & _ & Hmat & _) | (code & Hh2 & _)]].
      * rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
        injection Hmat as <-. exists (exist _ i Hns). split; reflexivity.
      * rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
      * rewrite Hh' in Hh2. discriminate.
    + apply HR in Hc. destruct (Hout _ Hc) as (i & Hi). exfalso. exact (Unmodeled_Ok _ _ _ Hi).
Qed.

Lemma node_family_succ : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event)
    (R : outcome SyscallEffect -> Prop),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> R o) ->
  (forall i, R (Ok (effs i) (ms' i) (evs i))) ->
  (forall o, R o -> exists i, o = Ok (effs i) (ms' i) (evs i)) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  injected_family_off CFG (sys_input segs ms x8) = true ->
  (exists i0, refusal_b (sys_input segs ms x8) model (eff_ret (effs i0)) = false) ->
  node_ok segs (mkCfg ms model)
    {i : I | refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false}
    (fun j => evs (proj1_sig j))
    (fun j => mkCfg (advance_past_svc (apply_effect ms (effs (proj1_sig j)))) (ms' (proj1_sig j))).
Proof.
  intros ms model x8 I effs ms' evs R Hh Hsvc HR Hin Hout Hh' Hlazy Hoff [i0 Hi0].
  destruct (node_family_cfg ms model x8 I effs ms' evs R Hh Hsvc HR Hin Hout Hh' Hlazy) as [H1 H2].
  split.
  - intros [i Hi]. cbn [proj1_sig].
    exact (H1 (exist _ i (not_spurious_of_not_refusal _ _ _ Hi))).
  - intros e st Hss. destruct (H2 e st Hss) as ([i Hns] & -> & ->). cbn [proj1_sig].
    destruct (refusal_b (sys_input segs ms x8) model (eff_ret (effs i))) eqn:Er.
    + exfalso. apply Hns.
      apply (spurious_of_refusal _ _ _ (effs i0) (ms' i0) (evs i0) Hoff Er); [| exact Hi0].
      apply HR. apply Hin.
    + exists (exist _ i Er). split; reflexivity.
Qed.

Lemma node_family_forced : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event)
    (R : outcome SyscallEffect -> Prop),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> R o) ->
  (forall i, R (Ok (effs i) (ms' i) (evs i))) ->
  (forall o, R o -> exists i, o = Ok (effs i) (ms' i) (evs i)) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = true) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs R Hh Hsvc HR Hin Hout Hh' Hlazy Hall.
  destruct (node_family_cfg ms model x8 I effs ms' evs R Hh Hsvc HR Hin Hout Hh' Hlazy) as [H1 H2].
  assert (Hns : forall i, ~ spurious_refusal_cfg CFG (sys_input segs ms x8) model (effs i)).
  { intros i. apply not_spurious_forced. intros eff' m' evs' Hs.
    apply HR in Hs. destruct (Hout _ Hs) as (j & Hj). apply Ok_inj in Hj as (-> & _ & _).
    apply Hall. }
  split.
  - intros i. exact (H1 (exist _ i (Hns i))).
  - intros e st Hss. destruct (H2 e st Hss) as ([i Hi] & -> & ->). exists i. split; reflexivity.
Qed.

Lemma family_cfg_nonempty : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event)
    (R : outcome SyscallEffect -> Prop),
  (forall o, syscall_spec (sys_input segs ms x8) model o <-> R o) ->
  (forall o, R o -> exists i, o = Ok (effs i) (ms' i) (evs i)) ->
  I ->
  {i : I | ~ spurious_refusal_cfg CFG (sys_input segs ms x8) model (effs i)}.
Proof.
  intros ms model x8 I effs ms' evs R HR Hout i0.
  apply constructive_indefinite_description.
  destruct (classic (spurious_refusal_cfg CFG (sys_input segs ms x8) model (effs i0))) as [Hsp | Hns].
  - destruct Hsp as (_ & _ & (eff' & m' & evs' & Hs & Hnr)).
    apply HR in Hs. destruct (Hout _ Hs) as (j & Hj). apply Ok_inj in Hj as (-> & _ & _).
    exists j. apply not_spurious_of_not_refusal. exact Hnr.
  - exists i0. exact Hns.
Qed.

End WithSegs.
