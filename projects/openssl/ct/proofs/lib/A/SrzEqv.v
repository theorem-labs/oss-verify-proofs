(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's segment list) and LPS 20f40762 (vdso_post writes at most the first F bytes of the draw's frame). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.openssl.ct.lib.AS Require Import ShapeAlg SpinAlg.
From OSSVerify.Proofs.openssl.ct.lib.Common Require Import RegEqv.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Cfg Require RomBase.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section Eqv.
Variable segs : list Segment.

Definition ms_with_regs (ms : machine_state) (R : bvmap 5 word) : machine_state :=
  {| ms_regs := R; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms; ms_svc_pending := ms_svc_pending ms;
     ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms; ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.

(** the registers a vDSO call leaves, from the caller's state and the call's return
    value: [vdso_post] reads the effect only through [eff_ret] for its registers *)
Definition vdso_regs (ms : machine_state) (model : Model) (ret : word) : bvmap 5 word :=
  ms_regs (vdso_post segs ms model (vdso_frame segs) (mkEffect ret [] [])).

(* [comment removed for export] *)
Definition succ_eqv (c2 x : config) : config :=
  match ms_svc_pending (cfg_ms c2) with
  | None => match mi_account_step segs (cfg_ms c2) (cfg_model c2) with
            | MachineOk (ms', mo') => mkCfg ms' mo'
            | _ => mkCfg (ms_with_regs (cfg_ms x) (vdso_regs (cfg_ms c2) (cfg_model c2) (reg_get (ms_regs (cfg_ms x)) 10)))
                         (cfg_model x)
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

Lemma ms_with_regs_eta : forall ms, ms_with_regs ms (ms_regs ms) = ms.
Proof. intros []. reflexivity. Qed.

Lemma write_regs_shape : forall rs vs ms,
  vdso_write_regs ms rs vs = ms_with_regs ms (ms_regs (vdso_write_regs ms rs vs)).
Proof.
  induction rs as [|r rs IH]; intros [|v vs] ms; cbn [vdso_write_regs]; try (symmetry; apply ms_with_regs_eta).
  etransitivity; [apply IH|].
  unfold set_reg. destruct (bv_eqb (Z_to_bv 5 r) 0); reflexivity.
Qed.

(* The register-free shape of a vDSO call.  Proved by rewriting through
   small record lemmas, never by [cbn] or conversion on [vdso_post] itself:
   those unfold the caller-saved list and the bitvector constants and
   exhausted the build's memory. *)
Lemma with_regs_with_regs : forall ms R1 R2, ms_with_regs (ms_with_regs ms R1) R2 = ms_with_regs ms R2.
Proof. intros [] R1 R2. reflexivity. Qed.

Lemma mem_with_regs : forall ms R, ms_mem (ms_with_regs ms R) = ms_mem ms.
Proof. intros [] R. reflexivity. Qed.

Lemma vdso_with_mem_with_regs : forall ms R m, vdso_with_mem (ms_with_regs ms R) m = ms_with_regs (vdso_with_mem ms m) R.
Proof. intros [] R m. reflexivity. Qed.

Lemma with_regs_vdso_set_pc : forall X R pc, ms_with_regs (vdso_set_pc X pc) R = vdso_set_pc (ms_with_regs X R) pc.
Proof. intros [] R pc. reflexivity. Qed.

Lemma with_regs_apply_effect : forall Y R' R eff,
  ms_with_regs (apply_effect (ms_with_regs Y R') eff) R = ms_with_regs (apply_effect Y eff) R.
Proof.
  intros [] R' R eff. unfold apply_effect, set_reg, ms_with_regs.
  destruct (bv_eqb (10 : reg) 0); reflexivity.
Qed.

Lemma with_regs_eqv : forall ms1 ms2, ms_eqv ms1 ms2 -> ms_with_regs ms1 (ms_regs ms2) = ms2.
Proof.
  intros [R1 F1 p1 s1 rv1 fc1 m1 ro1] [R2 F2 p2 s2 rv2 fc2 m2 ro2] (_ & Hf & Hp & Hs & Hrv & Hfc & Hm & Hrom).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in Hf, Hp, Hs, Hrv, Hfc, Hm, Hrom.
  subst. reflexivity.
Qed.

Lemma vdso_with_mem_eqv_regs : forall ms1 ms2 m, ms_eqv ms1 ms2 ->
  ms_with_regs (vdso_with_mem ms1 m) (ms_regs ms2) = vdso_with_mem ms2 m.
Proof.
  intros ms1 ms2 m H. rewrite <- vdso_with_mem_with_regs, (with_regs_eqv _ _ H). reflexivity.
Qed.

Lemma apply_effect_regs : forall ms eff,
  ms_regs (apply_effect ms eff) = ms_regs (set_reg ms 10 (eff_ret eff)).
Proof. intros ms eff. reflexivity. Qed.

Lemma vdso_post_regs : forall ms model f eff,
  ms_regs (vdso_post segs ms model f eff) = ms_regs (vdso_post segs ms model f (mkEffect (eff_ret eff) [] [])).
Proof.
  intros ms model f eff. unfold vdso_post. cbv zeta.
  change (eff_ret (mkEffect (eff_ret eff) [] [])) with (eff_ret eff).
  set (Z := vdso_with_mem _ _).
  change (ms_regs (vdso_set_pc (apply_effect Z eff) (ms_reg ms 1)))
    with (ms_regs (apply_effect Z eff)).
  change (ms_regs (vdso_set_pc (apply_effect Z (mkEffect (eff_ret eff) [] [])) (ms_reg ms 1)))
    with (ms_regs (apply_effect Z (mkEffect (eff_ret eff) [] []))).
  rewrite !apply_effect_regs. reflexivity.
Qed.

(* LPS 08b1429 ([vdso_post] reads the stack pointer, the caller-saved registers and the
   memory view): the three facts over this file's [Common.RegEqv.ms_eqv], as
   [Lib.RegsEquiv] states them over its own. *)
Lemma ms_sp_eqv : forall ms1 ms2, ms_eqv ms1 ms2 -> ms_sp ms1 = ms_sp ms2.
Proof.
  intros ms1 ms2 H. unfold ms_sp. apply (proj1 H).
  all: intros Hc; apply (f_equal (@bv_unsigned 5)) in Hc; vm_compute in Hc; discriminate Hc.
Qed.

Lemma ms_read_byte_eqv : forall ms1 ms2, ms_eqv ms1 ms2 -> ms_read_byte ms1 = ms_read_byte ms2.
Proof.
  intros ms1 ms2 (HR & Hf & Hp & Hs & Hrv & Hfc & Hm & Hrom).
  unfold ms_read_byte. rewrite Hm, Hrom. reflexivity.
Qed.

Lemma vdso_read_regs_eqv : forall ms1 ms2, ms_eqv ms1 ms2 -> vdso_read_regs ms1 = vdso_read_regs ms2.
Proof.
  intros ms1 ms2 H. unfold vdso_read_regs. apply List.map_ext.
  intros r. apply (ms_reg_eqv _ _ _ H).
Qed.

(** a vDSO call from two [ms_eqv] states lands in states that differ in their
    registers only *)
Lemma vdso_post_other : forall ms1 ms2 model f eff R, ms_eqv ms1 ms2 ->
  ms_with_regs (vdso_post segs ms1 model f eff) R = ms_with_regs (vdso_post segs ms2 model f eff) R.
Proof.
  intros ms1 ms2 model f eff R H.
  unfold vdso_post. cbv zeta.
  rewrite (ms_reg_eqv _ _ 1 H), (ms_sp_eqv _ _ H), (vdso_read_regs_eqv _ _ H), (ms_read_byte_eqv _ _ H).
  set (ra := ms_reg ms2 1). set (lo := ms_sp ms2 - Z_to_bv 64 (Z.of_N f)).
  set (left := vdr_draw _ _ _ _ _).
  rewrite (write_regs_shape _ _ ms1), (write_regs_shape _ _ ms2).
  set (R1 := ms_regs (vdso_write_regs ms1 vdso_caller_saved (vl_regs left))).
  set (R2 := ms_regs (vdso_write_regs ms2 vdso_caller_saved (vl_regs left))).
  rewrite !mem_with_regs.
  replace (ms_mem ms1) with (ms_mem ms2) by (symmetry; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))).
  set (M := vdso_write_frame segs (ms_mem ms2) lo (firstn (N.to_nat f) (vl_frame left))).
  rewrite !vdso_with_mem_with_regs, !with_regs_vdso_set_pc, !with_regs_apply_effect.
  rewrite <- (with_regs_apply_effect (vdso_with_mem ms1 M) (ms_regs ms2)).
  rewrite (vdso_with_mem_eqv_regs _ _ _ H). reflexivity.
Qed.

Lemma vdso_post_ret : forall ms model f eff,
  reg_get (ms_regs (vdso_post segs ms model f eff)) 10 = eff_ret eff.
Proof.
  intros. unfold vdso_post, vdso_set_pc, apply_effect. cbv zeta. cbn [ms_regs].
  unfold set_reg. replace (bv_eqb (10 : reg) 0) with false by reflexivity. cbn [ms_regs].
  apply reg_get_set_same.
Qed.

Lemma succ_vdso : forall ms1 ms2 model eff model'', ms_eqv ms1 ms2 ->
  ms_svc_pending ms2 = None -> mi_account_step segs ms2 model = MachineUnmodeled ->
  succ_eqv (mkCfg ms2 model) (mkCfg (vdso_post segs ms1 model (vdso_frame segs) eff) model'')
  = mkCfg (vdso_post segs ms2 model (vdso_frame segs) eff) model''.
Proof.
  intros ms1 ms2 model eff model'' H Hsvc Hacc.
  unfold succ_eqv. cbn [cfg_ms cfg_model]. rewrite Hsvc, Hacc. f_equal.
  rewrite vdso_post_ret. unfold vdso_regs.
  rewrite (vdso_post_other ms1 ms2 model (vdso_frame segs) eff _ H).
  rewrite <- (vdso_post_regs ms2 model (vdso_frame segs) eff).
  apply ms_with_regs_eta.
Qed.

(* [comment removed for export] *)
Lemma succ_eqv_fwd : forall c1 c2 e x, cfg_eqv c1 c2 -> sstep_cfg segs ncfg c1 e (SNext x) ->
  sstep_cfg segs ncfg c2 e (SNext (succ_eqv c2 x)) /\ cfg_eqv x (succ_eqv c2 x).
Proof.
  intros [ms1 mo1] [ms2 mo2] e x [Hms Hmo] H. cbn [cfg_ms cfg_model] in *. subst mo2.
  pose proof Hms as Hms0. destruct Hms as (HR & Hf & Hp & Hs & Hrv & Hfc & Hm & Hrom).
  inversion H as [ms model ms' model' Hh Hsvc Hacc | |
                 | ms model fn n eff model' model'' evs' Hh Hsvc Hacc Hfn Hno Hspec Hef Hh' Hmat | |
                 | ms model x8 eff model' model'' evs' Hh Hsvc Hspec Hnsp Hh' Hmat |
                 | ms model x8 eff model' evs' code Hh Hsvc Hspec Hh' Hk
                 | ms model x8 eff model' evs' sig Hh Hsvc Hspec Hk | ]; subst.
  - (* [comment removed for export] *)
    pose proof (mi_account_step_eqv segs ms1 ms2 mo1 Hms0) as HA. rewrite Hacc in HA.
    destruct (mi_account_step segs ms2 mo1) as [[a2 m2]| |] eqn:E2; try contradiction.
    destruct HA as [HA Hm2]. subst m2.
    unfold succ_eqv. cbn [cfg_ms cfg_model]. rewrite <- Hs, Hsvc, E2.
    split; [apply sstep_cfg_instr; auto; rewrite <- Hs; exact Hsvc | split; [exact HA | reflexivity]].
  - (* the vDSO call: c2's successor is c1's with c2's register map *)
    pose proof (mi_account_step_eqv segs ms1 ms2 mo1 Hms0) as HA. rewrite Hacc in HA.
    destruct (mi_account_step segs ms2 mo1) as [[a2 m2]| |] eqn:E2; try contradiction.
    rewrite (succ_vdso ms1 ms2 mo1 eff (with_vdso_bump model'') Hms0 ltac:(rewrite <- Hs; exact Hsvc) E2).
    split.
    + eapply sstep_cfg_vdso_call;
        [exact Hh | rewrite <- Hs; exact Hsvc | exact E2 | unfold ms_pc; rewrite <- Hp; exact Hfn | exact Hno
        | rewrite <- (sys_input_eqv segs ms1 ms2 _ Hms0); exact Hspec | exact Hef | exact Hh' | exact Hmat].
    + split; [apply (vdso_post_eqv segs); exact Hms0 | reflexivity].
  - (* [comment removed for export] *)
    assert (Hx : succ_eqv (mkCfg ms2 mo1) (mkCfg (advance_past_svc (apply_effect ms1 eff)) model'')
                 = mkCfg (advance_past_svc (apply_effect ms2 eff)) model'').
    { unfold succ_eqv. cbn [cfg_ms cfg_model]. rewrite <- Hs, Hsvc. cbn [advance_past_svc ms_svc_pending].
      rewrite (apply_effect_with_regs ms1 ms2 eff Hms0). reflexivity. }
    rewrite Hx. split.
    + eapply sstep_cfg_syscall; eauto; [rewrite <- Hs; exact Hsvc | rewrite <- (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hspec
                                         | rewrite <- (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hnsp].
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
Lemma succ_eqv_bwd : forall c1 c2 e st, cfg_eqv c1 c2 -> sstep_cfg segs ncfg c2 e st ->
(exists x, sstep_cfg segs ncfg c1 e (SNext x) /\ st = SNext (succ_eqv c2 x)) \/ sstep_cfg segs ncfg c1 e SError.
Proof.
intros [ms1 mo1] [ms2 mo2] e st [Hms Hmo] H. cbn [cfg_ms cfg_model] in *. subst mo2.
pose proof Hms as Hms0. destruct Hms as (HR & Hf & Hp & Hs & Hrv & Hfc & Hm & Hrom).
inversion H as [ms model ms' model' Hh Hsvc Hacc | ms model Hh Hsvc Hacc | ms model Hh Hsvc Hacc Hnv
| ms model fn n eff model' model'' evs' Hh Hsvc Hacc Hfn Hno Hspec Hef Hh' Hmat
| ms model fn n eff model' evs' Hh Hsvc Hacc Hfn Hno Hspec Hef Hh' Hmat
| ms model fn Hh Hsvc Hacc Hfn Hun
| ms model x8 eff model' model'' evs' Hh Hsvc Hspec Hnsp Hh' Hmat
| ms model x8 eff model' evs' Hh Hsvc Hspec Hnsp Hh' Hmat
| ms model x8 eff model' evs' code Hh Hsvc Hspec Hh' Hk
| ms model x8 eff model' evs' sig Hh Hsvc Hspec Hk
| ms model x8 Hh Hsvc Hspec]; subst.
-
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
right. eapply sstep_cfg_instr_unmodeled; [exact Hh | rewrite Hs; exact Hsvc | exact E1 | unfold ms_pc; rewrite Hp; exact Hnv].
-
pose proof (mi_account_step_eqv segs ms1 ms2 mo1 Hms0) as HA. rewrite Hacc in HA.
destruct (mi_account_step segs ms1 mo1) as [[a1 m1]| |] eqn:E1; try contradiction.
left. exists (mkCfg (vdso_post segs ms1 mo1 (vdso_frame segs) eff) (with_vdso_bump model'')). split.
+ eapply sstep_cfg_vdso_call;
[exact Hh | rewrite Hs; exact Hsvc | exact E1 | unfold ms_pc; rewrite Hp; exact Hfn | exact Hno
| rewrite (sys_input_eqv segs ms1 ms2 _ Hms0); exact Hspec | exact Hef | exact Hh' | exact Hmat].
+ f_equal. symmetry. apply succ_vdso; [exact Hms0 | exact Hsvc | exact Hacc].
- pose proof (mi_account_step_eqv segs ms1 ms2 mo1 Hms0) as HA. rewrite Hacc in HA.
destruct (mi_account_step segs ms1 mo1) as [[a1 m1]| |] eqn:E1; try contradiction.
right. eapply sstep_cfg_vdso_materialization_fault;
[exact Hh | rewrite Hs; exact Hsvc | exact E1 | unfold ms_pc; rewrite Hp; exact Hfn | exact Hno
| rewrite (sys_input_eqv segs ms1 ms2 _ Hms0); exact Hspec | exact Hef | exact Hh' | exact Hmat].
- pose proof (mi_account_step_eqv segs ms1 ms2 mo1 Hms0) as HA. rewrite Hacc in HA.
destruct (mi_account_step segs ms1 mo1) as [[a1 m1]| |] eqn:E1; try contradiction.
right. eapply sstep_cfg_vdso_unmodeled;
[exact Hh | rewrite Hs; exact Hsvc | exact E1 | unfold ms_pc; rewrite Hp; exact Hfn
| exact (vdso_call_unmodeled_eqv segs ms1 ms2 mo1 fn Hms0 Hun)].
-  left.
exists (mkCfg (advance_past_svc (apply_effect ms1 eff)) model''). split.
+ eapply sstep_cfg_syscall; eauto; [rewrite Hs; exact Hsvc | rewrite (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hspec
| rewrite (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hnsp].
+ unfold succ_eqv. cbn [cfg_ms cfg_model]. rewrite Hsvc. cbn [advance_past_svc ms_svc_pending].
rewrite (apply_effect_with_regs ms1 ms2 eff Hms0). reflexivity.
- right. eapply sstep_cfg_syscall_materialization_fault; eauto; [rewrite Hs; exact Hsvc | rewrite (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hspec
| rewrite (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hnsp].
-  left. exists (mkCfg ms1 model'). split.
+ eapply sstep_cfg_exit; eauto; [rewrite Hs; exact Hsvc | rewrite (sys_input_eqv segs ms1 ms2 x8 Hms0); exact Hspec].
+ unfold succ_eqv. cbn [cfg_ms cfg_model]. rewrite Hsvc, Hs, Hsvc. reflexivity.
-  left. exists (mkCfg ms1 model'). split.
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

(* LPS 08b1429: [RomBase.sys_rob] carries along [cfg_eqv] (the same input: [sys_input_eqv]).
   From openssl/punycode's [A/SrzEqv.v]. *)
Lemma sys_rob_eqv : forall c1 c2, cfg_eqv c1 c2 -> RomBase.sys_rob segs c1 -> RomBase.sys_rob segs c2.
Proof.
  intros [ms1 m1] [ms2 m2] [Hms Hm] Hrob r x8 Hr Hs o. cbn [cfg_ms cfg_model] in *. subst m2.
  pose proof Hms as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  assert (Hw : ms_eqv (RomBase.wrom ms1 r) (RomBase.wrom ms2 r))
    by (unfold ms_eqv, RomBase.wrom; cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom];
        repeat split; assumption).
  rewrite <- (sys_input_eqv segs _ _ x8 Hw), <- (sys_input_eqv segs ms1 ms2 x8 Hms).
  apply Hrob; cbn [cfg_ms]; [rewrite H8; exact Hr | rewrite H4; exact Hs].
Qed.

(* [comment removed for export] *)
Theorem realizes_eqv : forall c1 T, realizes segs c1 T -> forall c2, cfg_eqv c1 c2 -> realizes segs c2 T.
Proof.
  intros c1 T H. induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq]; intros c2 Heqv.
  - apply (rz_node segs c2 I evs (fun i => succ_eqv c2 (nx i)) T i0);
      [exact (node_ok_eqv c c2 I evs nx Heqv Hnode) | exact (sys_rob_eqv c c2 Heqv Hrob) |].
    intros i. apply (IH i). exact (proj2 (succ_eqv_fwd c c2 (evs i) (nx i) Heqv (proj1 Hnode i))).
  - apply rz_halt. destruct Heqv as [_ Hmo]. rewrite <- Hmo. exact Hh.
  - eapply rz_conseq; [apply (IH c2 Heqv) | exact Heq].
Qed.

Theorem srealizes_of_realizes_eqv : forall c1 c2 T, realizes segs c1 T -> cfg_eqv c1 c2 -> srealizes segs c2 T.
Proof. intros c1 c2 T H He. apply srealizes_of_realizes. exact (realizes_eqv c1 T H c2 He). Qed.

End Eqv.
