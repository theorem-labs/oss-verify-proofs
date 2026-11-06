(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AS Require Import ShapeAlg SpinAlg.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Common Require Import RegEqv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section Eqv.
Variable segs : list Segment.
Notation scfg := CfgStep.kit_cfg (only parsing).

Definition ms_with_regs (ms : machine_state) (R : bvmap 5 word) : machine_state :=
  {| ms_regs := R; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms; ms_svc_pending := ms_svc_pending ms;
     ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms; ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.

(* [comment removed for export] *)
Definition succ_eqv (c2 x : config) : config :=
  match ms_svc_pending (cfg_ms c2) with
  | None => match mi_account_step segs (cfg_ms c2) (cfg_model c2) with
            | MachineOk (ms', mo') => mkCfg ms' mo'
            | _ => x
            end
  | Some _ => match ms_svc_pending (cfg_ms x) with
              | None => mkCfg (ms_with_regs (cfg_ms x) (ms_regs (set_reg (cfg_ms c2) 10 (reg_get (ms_regs (cfg_ms x)) 10))))
                              (cfg_model x)
              | Some _ => mkCfg (cfg_ms c2) (cfg_model x)
              end
  end.

Lemma reg_get_set_same : forall (R : bvmap 5 word) (k : reg) v, reg_get (bvmap_set k v R) k = v.
Proof. intros R k v. unfold reg_get. rewrite bvmap_get_set_same. reflexivity. Qed.

(* [comment removed for export] *)
Lemma apply_effect_with_regs : forall ms1 ms2 eff, ms_eqv ms1 ms2 ->
  advance_past_svc (apply_effect ms2 eff)
  = ms_with_regs (advance_past_svc (apply_effect ms1 eff))
                 (ms_regs (set_reg ms2 10 (reg_get (ms_regs (advance_past_svc (apply_effect ms1 eff))) 10))).
Proof.
  intros [R1 F1 p1 s1 rv1 fc1 m1 ro1] [R2 F2 p2 s2 rv2 fc2 m2 ro2] eff (HR & Hf & Hp & Hs & Hrv & Hfc & Hm & Hrom).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *. subst.
  unfold advance_past_svc, apply_effect, set_reg, ms_with_regs, ms_pc. cbn.
  replace (bv_eqb (10 : reg) 0) with false by reflexivity. cbn.
  rewrite reg_get_set_same. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma succ_eqv_fwd : forall c1 c2 e x, cfg_eqv c1 c2 -> sstep_cfg segs scfg c1 e (SNext x) ->
  sstep_cfg segs scfg c2 e (SNext (succ_eqv c2 x)) /\ cfg_eqv x (succ_eqv c2 x).
Proof.
  intros [ms1 mo1] [ms2 mo2] e x [Hms Hmo] H. cbn [cfg_ms cfg_model] in *. subst mo2.
  pose proof Hms as Hms0. destruct Hms as (HR & Hf & Hp & Hs & Hrv & Hfc & Hm & Hrom).
  inversion H as [ms model ms' model' Hh Hsvc Hacc | | | ms model x8 eff model' model'' evs' Hh Hsvc Hspec Hns Hh' Hmat |
                 | ms model x8 eff model' evs' code Hh Hsvc Hspec Hh' Hk
                 | ms model x8 eff model' evs' sig Hh Hsvc Hspec Hk | ]; subst.
  - (* [comment removed for export] *)
    pose proof (mi_account_step_eqv segs ms1 ms2 mo1 Hms0) as HA. rewrite Hacc in HA.
    destruct (mi_account_step segs ms2 mo1) as [[a2 m2]| |] eqn:E2; try contradiction.
    destruct HA as [HA Hm2]. subst m2.
    unfold succ_eqv. cbn [cfg_ms cfg_model]. rewrite <- Hs, Hsvc, E2.
    split; [apply sstep_cfg_instr; auto; rewrite <- Hs; exact Hsvc | split; [exact HA | reflexivity]].
  - (* [comment removed for export] *)
    assert (Hx : succ_eqv (mkCfg ms2 mo1) (mkCfg (advance_past_svc (apply_effect ms1 eff)) model'')
                 = mkCfg (advance_past_svc (apply_effect ms2 eff)) model'').
    { unfold succ_eqv. cbn [cfg_ms cfg_model]. rewrite <- Hs, Hsvc. cbn [advance_past_svc ms_svc_pending].
      rewrite (apply_effect_with_regs ms1 ms2 eff Hms0). reflexivity. }
    rewrite Hx. split.
    + eapply sstep_cfg_syscall; eauto; [rewrite <- Hs; exact Hsvc | rewrite <- (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hspec | rewrite <- (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hns].
    + split; [apply apply_effect_eqv, Hms0 | reflexivity].
  - (* [comment removed for export] *)
    assert (Hx : succ_eqv (mkCfg ms2 mo1) (mkCfg ms1 model') = mkCfg ms2 model').
    { unfold succ_eqv. cbn [cfg_ms cfg_model]. rewrite <- Hs, Hsvc. reflexivity. }
    rewrite Hx. split; [|split; [exact Hms0 | reflexivity]].
    eapply sstep_cfg_exit; eauto; [rewrite <- Hs; exact Hsvc | rewrite <- (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hspec].
  - (* [comment removed for export] *)
    assert (Hx : succ_eqv (mkCfg ms2 mo1) (mkCfg ms1 model') = mkCfg ms2 model').
    { unfold succ_eqv. cbn [cfg_ms cfg_model]. rewrite <- Hs, Hsvc. reflexivity. }
    rewrite Hx. split; [|split; [exact Hms0 | reflexivity]].
    eapply sstep_cfg_killed; eauto; [rewrite <- Hs; exact Hsvc | rewrite <- (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hspec].
Qed.

(* [comment removed for export] *)
Lemma succ_eqv_bwd : forall c1 c2 e st, cfg_eqv c1 c2 -> sstep_cfg segs scfg c2 e st ->
  (exists x, sstep_cfg segs scfg c1 e (SNext x) /\ st = SNext (succ_eqv c2 x)) \/ sstep_cfg segs scfg c1 e SError.
Proof.
  intros [ms1 mo1] [ms2 mo2] e st [Hms Hmo] H. cbn [cfg_ms cfg_model] in *. subst mo2.
  pose proof Hms as Hms0. destruct Hms as (HR & Hf & Hp & Hs & Hrv & Hfc & Hm & Hrom).
  inversion H as [ms model ms' model' Hh Hsvc Hacc | ms model Hh Hsvc Hacc | ms model Hh Hsvc Hacc
                 | ms model x8 eff model' model'' evs' Hh Hsvc Hspec Hns Hh' Hmat
                 | ms model x8 eff model' evs' Hh Hsvc Hspec Hns Hh' Hmat
                 | ms model x8 eff model' evs' code Hh Hsvc Hspec Hh' Hk
                 | ms model x8 eff model' evs' sig Hh Hsvc Hspec Hk
                 | ms model x8 Hh Hsvc Hspec]; subst.
  - (* [comment removed for export] *)
    pose proof (mi_account_step_eqv segs ms1 ms2 mo1 Hms0) as HA. rewrite Hacc in HA.
    destruct (mi_account_step segs ms1 mo1) as [[a1 m1]| |] eqn:E1; try contradiction.
    destruct HA as [HA Hm1]. subst m1. left.
    exists (mkCfg a1 model'). split; [apply sstep_cfg_instr; auto; rewrite Hs; exact Hsvc|].
    unfold succ_eqv. cbn [cfg_ms cfg_model]. rewrite Hsvc, Hacc. reflexivity.
  - pose proof (mi_account_step_eqv segs ms1 ms2 mo1 Hms0) as HA. rewrite Hacc in HA.
    destruct (mi_account_step segs ms1 mo1) as [[a1 m1]| |] eqn:E1; try contradiction.
    right. apply sstep_cfg_instr_fault; auto; rewrite Hs; exact Hsvc.
  - pose proof (mi_account_step_eqv segs ms1 ms2 mo1 Hms0) as HA. rewrite Hacc in HA.
    destruct (mi_account_step segs ms1 mo1) as [[a1 m1]| |] eqn:E1; try contradiction.
    right. apply sstep_cfg_instr_unmodeled; auto; rewrite Hs; exact Hsvc.
  - (* [comment removed for export] *) left.
    exists (mkCfg (advance_past_svc (apply_effect ms1 eff)) model''). split.
    + eapply sstep_cfg_syscall; eauto; [rewrite Hs; exact Hsvc | rewrite (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hspec | rewrite (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hns].
    + unfold succ_eqv. cbn [cfg_ms cfg_model]. rewrite Hsvc. cbn [advance_past_svc ms_svc_pending].
      rewrite (apply_effect_with_regs ms1 ms2 eff Hms0). reflexivity.
  - right. eapply sstep_cfg_syscall_materialization_fault; eauto; [rewrite Hs; exact Hsvc | rewrite (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hspec | rewrite (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hns].
  - (* [comment removed for export] *) left. exists (mkCfg ms1 model'). split.
    + eapply sstep_cfg_exit; eauto; [rewrite Hs; exact Hsvc | rewrite (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hspec].
    + unfold succ_eqv. cbn [cfg_ms cfg_model]. rewrite Hsvc, Hs, Hsvc. reflexivity.
  - (* [comment removed for export] *) left. exists (mkCfg ms1 model'). split.
    + eapply sstep_cfg_killed; eauto; [rewrite Hs; exact Hsvc | rewrite (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hspec].
    + unfold succ_eqv. cbn [cfg_ms cfg_model]. rewrite Hsvc, Hs, Hsvc. reflexivity.
  - right. eapply sstep_cfg_syscall_unmodeled; eauto; [rewrite Hs; exact Hsvc | rewrite (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hspec].
Qed.

Lemma node_ok_eqv : forall c1 c2 (I : Type) evs nx, cfg_eqv c1 c2 ->
  node_ok segs c1 I evs nx -> node_ok segs c2 I evs (fun i => succ_eqv c2 (nx i)).
Proof.
  intros c1 c2 I evs nx Heqv [Hfw Hbw]. split.
  - intros i. exact (proj1 (succ_eqv_fwd c1 c2 (evs i) (nx i) Heqv (Hfw i))).
  - intros e st Hst. destruct (succ_eqv_bwd c1 c2 e st Heqv Hst) as [(x & Hx & ->) | Herr].
    + destruct (Hbw e (SNext x) Hx) as (i & -> & Hxi). injection Hxi as Hxi. exists i. split; [reflexivity | rewrite Hxi; reflexivity].
    + destruct (Hbw e SError Herr) as (i & _ & Hc). discriminate Hc.
Qed.

(* [comment removed for export] *)
Theorem realizes_eqv : forall c1 T, realizes segs c1 T -> forall c2, cfg_eqv c1 c2 -> realizes segs c2 T.
Proof.
  intros c1 T H. induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq]; intros c2 Heqv.
  - apply (rz_node segs c2 I evs (fun i => succ_eqv c2 (nx i)) T i0); [exact (node_ok_eqv c c2 I evs nx Heqv Hnode)|].
    intros i. apply (IH i). exact (proj2 (succ_eqv_fwd c c2 (evs i) (nx i) Heqv (proj1 Hnode i))).
  - apply rz_halt. destruct Heqv as [_ Hmo]. rewrite <- Hmo. exact Hh.
  - eapply rz_conseq; [apply (IH c2 Heqv) | exact Heq].
Qed.

Theorem srealizes_of_realizes_eqv : forall c1 c2 T, realizes segs c1 T -> cfg_eqv c1 c2 -> srealizes segs c2 T.
Proof. intros c1 c2 T H He. apply srealizes_of_realizes. exact (realizes_eqv c1 T H c2 He). Qed.

End Eqv.
