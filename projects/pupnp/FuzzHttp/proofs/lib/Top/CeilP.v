(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's vDSO pair; walks lifted to the run's segment list; the launch's input, mmap base and entry draw). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling RunWord RegsEquiv InitStack EntrySecret.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import RomBase Realize RomStable.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

(* LPS 727298f3: the launch's machine state reads the mmap base and the entry draw, its model
   carries the vDSO draw, and the RUN reads the binary against [run_segments segs inp sp mb] from
   [init_config (run_segments ..) ..] ([Run.run_scfg]).  A walk over the binary's own segments
   from its own start gives the run's two fields through [RomStable.run_init]'s pieces: the walk
   moves to the run's read-only backing ([RomStable.realizes_run_rom], where the backing of
   [RegsEquiv.init_ms segs ..] is the binary's own) and the launch's machine state is the one
   [init_config] builds up to [RegsEquiv.ms_eqv]. *)
Lemma realizes_run_fields : forall segs pc ph sp brk mb rnd lim inp T,
  vdso_image segs = None ->
  realizes segs (mkCfg (init_ms segs pc ph sp mb rnd inp)
                       (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                          (init_model (segments_reserved segs) brk mb sp lim inp))) T ->
  ~ reaches_error_cfg (run_segments segs inp sp mb) ACFG
      (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp)
  /\ (forall tr, obs_trace_cfg (run_segments segs inp sp mb) ACFG
                   (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) tr <-> T tr).
Proof.
  intros segs pc ph sp brk mb rnd lim inp T Hvi HR.
  pose proof (realizes_run_rom segs inp sp mb (init_ms segs pc ph sp mb rnd inp)
                (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                   (init_model (segments_reserved segs) brk mb sp lim inp))
                T Hvi eq_refl HR) as HR'.
  (* [init_ms] reads its segment list only through the backing, so the lifted state is the run's *)
  change (wrom (init_ms segs pc ph sp mb rnd inp) (seg_rom1 (run_segments segs inp sp mb)))
    with (init_ms (run_segments segs inp sp mb) pc ph sp mb rnd inp) in HR'.
  rewrite <- (segments_reserved_run_segments segs inp sp mb) in HR'.
  unfold init_config.
  destruct (init_behaviour_scfg_eqv ACFG (run_segments segs inp sp mb) pc ph sp mb rnd inp
              (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
                 (init_model (segments_reserved (run_segments segs inp sp mb)) brk mb sp lim inp)))
    as (OT & RE & _).
  split.
  - intros E. apply RE in E. exact (realizes_no_error _ _ _ HR' E).
  - intros tr. rewrite (OT tr). apply (realizes_obs_iff _ _ _ HR').
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
