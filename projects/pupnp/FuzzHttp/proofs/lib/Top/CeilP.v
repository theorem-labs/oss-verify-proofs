(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling RunWord RegsEquiv InitStack EntrySecret.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Lemma realizes_run_fields : forall segs pc ph sp brk mb rnd lim inp T,
  realizes segs (mkCfg (init_ms segs pc ph sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rnd)
                       (init_model (segments_reserved segs) brk mb sp lim inp)) T ->
  ~ reaches_error_cfg segs ACFG (init_config segs pc ph sp brk mb rnd lim inp)
  /\ (forall tr, obs_trace_cfg segs ACFG (init_config segs pc ph sp brk mb rnd lim inp) tr <-> T tr).
Proof.
  intros segs pc ph sp brk mb rnd lim inp T HR. unfold init_config.
  destruct (init_behaviour_scfg_eqv ACFG segs pc ph sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rnd
              (init_model (segments_reserved segs) brk mb sp lim inp)) as (OT & RE & _).
  split.
  - intros E. apply RE in E. exact (realizes_no_error segs _ _ HR E).
  - intros tr. rewrite (OT tr). apply (realizes_obs_iff segs _ _ HR).
Qed.

Lemma ceil_range_of_valid_sp : forall sp, valid_sp sp ->
  alloc_floor <= bv_unsigned sp - stack_max_size <= alloc_ceiling_max.
Proof.
  intros sp (L & H & _). unfold alloc_floor, alloc_ceiling_max, sp_window_lo, sp_window_hi, stack_max_size in *. lia.
Qed.
Lemma ceil_al16_of_valid_sp : forall sp, valid_sp sp -> (bv_unsigned sp - stack_max_size) mod 16 = 0.
Proof.
  intros sp (_ & _ & M). unfold stack_max_size. rewrite Zminus_mod, M. reflexivity.
Qed.
Definition ceilP (sp : word) (V : valid_sp sp) : HasCeiling :=
  ceiling_of (bv_unsigned sp - stack_max_size) (ceil_range_of_valid_sp sp V) (ceil_al16_of_valid_sp sp V).
Definition guardP (d : EntryDraw) : HasGuard := run_guard (entry_guard d) (entry_secret d).

Lemma ceilP_eq : forall sp V, @alloc_ceiling (ceilP sp V) = bv_unsigned sp - stack_max_size.
Proof. intros; reflexivity. Qed.
