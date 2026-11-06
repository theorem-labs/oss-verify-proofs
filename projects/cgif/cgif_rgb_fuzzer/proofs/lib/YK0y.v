(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK16 YK0o YK0j YK0q YK15.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section a.
Variable segs : list Segment.
Definition halt_ev (m' : Model) (code : word) : event :=
match m_killed m' with
| Some sig => KillEv sig (m_fs m')
| None => ExitEv code (m_fs m')
end.
Lemma sstep_svc_inv : forall ms model x8 e st,
ms_svc_pending ms = Some x8 ->
sstep segs (mkCfg ms model) e st ->
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
intros ms model x8 e st Hsvc Hss.
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
sstep segs (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
intros ms model x8 eff m' evs Hh Hsvc Hc Hh' Hlazy.
apply (sstep_syscall segs ms model x8 eff m' m' evs Hh Hsvc).
- apply check_syscall_ok_iff. exact Hc.
- exact Hh'.
- apply materialize_model_accesses_no_lazy. exact Hlazy.
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
node_ok segs (mkCfg ms model) I evs
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hlazy. split.
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
node_ok segs (mkCfg ms model) I (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' Hh Hsvc Hok Hinv Hnu Hh' Hlazy.
apply (node_chk_ev ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok); auto.
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
Lemma rz_ret_only : forall ms model x8 r m' evs T,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
(forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' evs) ->
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
(forall eff, check_syscall (sys_input segs ms x8) eff model
= check_ret_only_copyins reads eff r m' evs) ->
m_halted m' = None ->
m_vm_lazy m' = [] ->
realizes segs (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
realizes segs (mkCfg ms model) (t_emit evs T).
Proof.
intros ms model x8 reads r m' evs T Hh Hsvc Hchk Hh' Hlazy Hc.
eapply rz_emit1; [eapply node_ret_only_copyins; eassumption | exact Hc].
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


End a.
