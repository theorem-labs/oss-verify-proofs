(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the channel-reader fact; the launch's input, mmap base and entry draw; the run's vDSO pair; the start-up walk lifted to the run's segment list through the section hypothesis SRZ_run). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode Ceiling RunWord RegsEquiv InitStack EntrySecret.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad Stdio Driver Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge TSim ShapeP0 CeilP.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require AssembleP0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require H_parser_inst AllocInst H_fuzz_stmt RDriver_ctx.
From OSSVerify.pupnp.FuzzHttp.images Require Plain.
From OSSVerify.pupnp.FuzzHttp.images Require Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import TSimS A0Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Notation tsh := (tshape node nstep nexit).

Section HandOff.
  Variable H_MAIN_A0 : ProcInput -> ExecEntry -> machine_state -> Model -> Prop.
  Definition at_main (inp : ProcInput) (en : ExecEntry) (c : config) : Prop := H_MAIN_A0 inp en (cfg_ms c) (cfg_model c).

  Record hmain_model_facts (inp : ProcInput) (mo : Model) : Prop := mkHMF {
    hk_fds : m_fds mo = [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ];
    hk_fs : m_fs mo = in_fs inp;
    hk_halted : m_halted mo = None;
    hk_tid : exists t, m_tid mo = Some t
  }.
  Hypothesis hmain_K : forall inp en ms mo, H_MAIN_A0 inp en ms mo -> hmain_model_facts inp mo.

  Variable RS_A : Z.
  Variable SRZ : list Segment -> config -> TSet -> Prop.
  Hypothesis SRZ_conseq : forall segs c T T', SRZ segs c T -> t_eq T T' -> SRZ segs c T'.
  Hypothesis SRZ_of_realizes : forall segs c T, realizes segs c T -> SRZ segs c T.
  Hypothesis SRZ_obs_iff : forall segs c T, SRZ segs c T -> forall tr, obs_trace_cfg segs ACFG c tr <-> T tr.
  Hypothesis SRZ_no_error : forall segs c T, SRZ segs c T -> ~ reaches_error_cfg segs ACFG c.
  (* LPS 727298f3: the run reads the binary against [run_segments] from [init_config] over it; a
     walk from the binary's own start is one from the run's ([SpinAlg.srun_init] for the walks
     [FinalA0] instantiates [SRZ] with). *)
  Hypothesis SRZ_run : forall segs inp (sp mb : word) pc ph brk rnd lim T,
    vdso_image segs = None ->
    SRZ segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
    SRZ (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.

  Definition HANDOFF : Prop :=
    forall inp en, valid_input inp -> valid_entry imgA0 en inp ->
      forall Tm : TSet, Tm [] -> (forall c, at_main inp en c -> SRZ asegs c Tm) -> SRZ asegs (cfgA0 en inp) Tm.

  Definition MAIN : Prop :=
    forall inp en c, valid_input inp -> valid_entry imgA0 en inp -> at_main inp en c ->
      realizes asegs c (T_A0main RS_A (in_argv inp) (cfg_model c)).

  Definition SHAPE : Prop :=
    forall (CP : HasCeiling) inp (spA brkA mbA : word) (dA : EntryDraw) en c,
      valid_input inp -> valid_entry imgP0 (mkEntry spA brkA mbA dA) inp -> valid_entry imgA0 en inp ->
      @alloc_ceiling CP = bv_unsigned spA - stack_max_size ->
      at_main inp en c ->
      t_incl0 (@AssembleP0.T_P0 CP (in_argv inp) (moP0 brkA mbA spA inp dA)) (T_A0main RS_A (in_argv inp) (cfg_model c))
      /\ t_incl0 (T_A0main RS_A (in_argv inp) (cfg_model c)) (@AssembleP0.T_P0 CP (in_argv inp) (moP0 brkA mbA spA inp dA)).

  Hypothesis HH : HANDOFF.
  Hypothesis HM : MAIN.
  Hypothesis HE : SHAPE.

  #[using="H_MAIN_A0 RS_A SRZ_conseq SRZ_of_realizes HH HM HE"] Lemma a0_realizes_P0_shape : forall (CP : HasCeiling) inp (spA brkA mbA : word) dA en,
    valid_input inp -> valid_entry imgP0 (mkEntry spA brkA mbA dA) inp -> valid_entry imgA0 en inp ->
    @alloc_ceiling CP = bv_unsigned spA - stack_max_size ->
    @AssembleP0.T_P0 CP (in_argv inp) (moP0 brkA mbA spA inp dA) [] ->
    SRZ asegs (cfgA0 en inp) (@AssembleP0.T_P0 CP (in_argv inp) (moP0 brkA mbA spA inp dA)).
  Proof.
    intros CP inp spA brkA mbA dA en VI VP VA CEIL NILP.
    apply (HH inp en VI VA); [exact NILP|]. intros c Hc.
    pose proof (HM inp en c VI VA Hc) as RZ.
    eapply SRZ_conseq; [apply SRZ_of_realizes; exact RZ|].
    destruct (HE CP inp spA brkA mbA dA en c VI VP VA CEIL Hc) as [I1 I2].
    apply t_eq_of_incl0; [exact (realizes_has_nil asegs _ _ RZ)| exact NILP| exact I2| exact I1].
  Qed.

  #[using="H_MAIN_A0 RS_A SRZ SRZ_conseq SRZ_of_realizes SRZ_obs_iff SRZ_no_error SRZ_run HH HM HE"] Theorem fuzzhttp_asan_error_free_of : strong_universal_error_free_T_scfg ACFG imgP0 imgA0.
  Proof.
    intros [spA brkA mbA dA] [spB brkB mbB dB] inp VA VB VI.
    pose proof VA as VA0. pose proof VB as VB0.
    pose proof (valid_input_va_size _ VI) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in VA. cbn [imgP0] in VA.
    destruct VA as (VSPA & VBRKA & VMBA & _ & LOKA). pose proof VI as (VARGV & VENVP & _).
    (* LPS 727298f3: the plain chain's launch facts from [valid_launch] and [entry_launch_ok_va] *)
    pose proof (stack_launch_ok_of_launch inp spA brkA mbA dA (valid_input_launch _ VI) LOKA) as ESFA.
    pose proof (@AssembleP0.p0_realizes (guardP dA) (ceilP spA VSPA) spA inp mbA dA brkA source_alloc_limit
                  VSPA eq_refl VARGV VENVP ESFA eq_refl eq_refl VBRKA VMBA (valid_input_channel_reader _ VI)
                  (@P0.H_parser_inst.fuzz_one_P0_closed (guardP dA) (ceilP spA VSPA))) as RA.
    (* the binary carries no vDSO segment; [eq_refl] is checked once [RA] has fixed the segment list *)
    pose proof (fun Hvi => realizes_run_fields _ _ _ _ _ _ _ _ _ _ Hvi RA) as RF.
    destruct (RF eq_refl) as [EA TA].
    pose proof (a0_realizes_P0_shape (ceilP spA VSPA) inp spA brkA mbA dA (mkEntry spB brkB mbB dB) VI VA0 VB0 (ceilP_eq spA VSPA)
                  (realizes_has_nil _ _ _ RA)) as RB.
    (* the walk from the binary's start is the run's ([SRZ_run]); [eq_refl] once [RB] has fixed the list *)
    pose proof (fun Hvi => SRZ_run asegs inp spB mbB Asan.M.init_pc Asan.M.phdrs brkB dB target_alloc_limit _ Hvi RB) as RB'.
    specialize (RB' eq_refl).
    unfold strong_equiv_error_free_scfg, error_free. cbn [run_scfg imgP0 imgA0 bh_errors bh_traces].
    split; [exact EA|]. split; [exact (SRZ_no_error _ _ _ RB')|].
    intros tr. rewrite (TA tr). symmetry. exact (SRZ_obs_iff _ _ _ RB' tr).
  Qed.
End HandOff.

Check (fuzzhttp_asan_error_free_of
        : forall H_MAIN_A0 RS_A SRZ, _ -> _ -> _ -> _ -> _ -> HANDOFF H_MAIN_A0 SRZ -> MAIN H_MAIN_A0 RS_A -> SHAPE H_MAIN_A0 RS_A ->
          strong_universal_error_free_T_scfg ACFG
            (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
            (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs)).

