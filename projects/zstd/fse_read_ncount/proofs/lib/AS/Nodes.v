(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import SimInv ExitSim CatSim FileSim ShapeAlg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Cfg.
Import ListNotations.
Open Scope bv_scope.
Section WithSegs.
Variable segs : list Segment.
Definition halt_ev (m' : Model) (code : word) : event :=
match m_killed m' with
| Some sig => KillEv sig (m_fs m')
| None => ExitEv code (m_fs m')
end.
#[using="Type"] Lemma sstep_svc_inv : forall ms model x8 e st,
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
#[using="Type"] Lemma uniform_not_spurious : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event) (b : bool),
(forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
(forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = b) ->
forall i, ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model (effs i).
Proof.
intros ms model x8 I effs ms' evs b Hinv Hb i (Hoff & Hr & eff' & m' & ev' & Hspec & Hnr).
apply check_syscall_ok_iff in Hspec.
destruct (Hinv _ _ _ Hspec) as (j & -> & _ & _).
rewrite Hb in Hr. rewrite Hb in Hnr. congruence.
Qed.
#[using="Type"] Lemma sstep_cfg_svc_inv_chk : forall ms model x8 e st,
ms_svc_pending ms = Some x8 ->
sstep_cfg segs ACFG (mkCfg ms model) e st ->
(exists eff model' evs,
check_syscall (sys_input segs ms x8) eff model = CheckOk model' evs
/\ ((~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff
/\ m_halted model' = None
/\ ((exists model'', e = evs
/\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
/\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
\/ (e = [] /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
/\ st = SError)))
\/ (exists code, m_halted model' = Some code
/\ e = evs ++ [halt_ev model' code]
/\ st = SNext (mkCfg ms model'))))
\/ (exists eff, check_syscall (sys_input segs ms x8) eff model = CheckUnmodeled
/\ e = [] /\ st = SError).
Proof.
intros ms model x8 e st Hsvc Hss.
inversion Hss; subst; try congruence.
- match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split.
+ apply check_syscall_ok_iff. eassumption.
+ left. split; [assumption|]. split; [assumption|]. left. eexists. repeat split; eauto.
- match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split.
+ apply check_syscall_ok_iff. eassumption.
+ left. split; [assumption|]. split; [assumption|]. right. repeat split; auto.
- match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split.
+ apply check_syscall_ok_iff. eassumption.
+ right. eexists. repeat split; eauto.
unfold halt_ev. match goal with Hk : m_killed _ = None |- _ => rewrite Hk end. reflexivity.
- match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
left. eexists _, _, _. split.
+ apply check_syscall_ok_iff. eassumption.
+ right.
match goal with Hk : m_killed ?mm = Some _ |- _ =>
destruct (m_halted mm) as [code|] eqn:Hhc;
[| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
exists code; split; [reflexivity | split; [unfold halt_ev; rewrite Hk; reflexivity | reflexivity]]
end.
- match goal with H : ms_svc_pending ms = Some ?y |- _ =>
rewrite Hsvc in H; inversion H; subst end.
right. exists (mkEffect (Z_to_bv 64 0) [] []). split; [|split; reflexivity].
apply check_syscall_err_iff. assumption.
Qed.
End WithSegs.
