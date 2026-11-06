(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.pupnp.FuzzHttp.images Require AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7 Require Import TSimS A0Prog.
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
      t_incl0 (@AssembleP0.T_P0 CP (in_argv inp) (moP0 brkA mbA spA inp)) (T_A0main RS_A (in_argv inp) (cfg_model c))
      /\ t_incl0 (T_A0main RS_A (in_argv inp) (cfg_model c)) (@AssembleP0.T_P0 CP (in_argv inp) (moP0 brkA mbA spA inp)).

  Hypothesis HH : HANDOFF.
  Hypothesis HM : MAIN.
  Hypothesis HE : SHAPE.

  #[using="H_MAIN_A0 RS_A SRZ_conseq SRZ_of_realizes HH HM HE"] Lemma a0_realizes_P0_shape : forall (CP : HasCeiling) inp (spA brkA mbA : word) dA en,
    valid_input inp -> valid_entry imgP0 (mkEntry spA brkA mbA dA) inp -> valid_entry imgA0 en inp ->
    @alloc_ceiling CP = bv_unsigned spA - stack_max_size ->
    @AssembleP0.T_P0 CP (in_argv inp) (moP0 brkA mbA spA inp) [] ->
    SRZ asegs (cfgA0 en inp) (@AssembleP0.T_P0 CP (in_argv inp) (moP0 brkA mbA spA inp)).
  Proof.
    intros CP inp spA brkA mbA dA en VI VP VA CEIL NILP.
    apply (HH inp en VI VA); [exact NILP|]. intros c Hc.
    pose proof (HM inp en c VI VA Hc) as RZ.
    eapply SRZ_conseq; [apply SRZ_of_realizes; exact RZ|].
    destruct (HE CP inp spA brkA mbA dA en c VI VP VA CEIL Hc) as [I1 I2].
    apply t_eq_of_incl0; [exact (realizes_has_nil asegs _ _ RZ)| exact NILP| exact I2| exact I1].
  Qed.

  #[using="H_MAIN_A0 RS_A SRZ SRZ_conseq SRZ_of_realizes SRZ_obs_iff SRZ_no_error HH HM HE"] Theorem fuzzhttp_asan_error_free_of : strong_universal_error_free_T_scfg ACFG imgP0 imgA0.
  Proof.
    intros [spA brkA mbA dA] [spB brkB mbB dB] inp VA VB VI.
    pose proof VA as VA0. pose proof VB as VB0.
    pose proof (valid_input_va_size _ VI) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in VA. cbn [imgP0] in VA.
    destruct VA as (VSPA & VBRKA & VMBA & ESFA). pose proof VI as (VARGV & VENVP & _).
    pose proof (@AssembleP0.p0_realizes (guardP dA) (ceilP spA VSPA) spA (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) dA
                  brkA mbA source_alloc_limit inp VSPA eq_refl VARGV VENVP ESFA eq_refl eq_refl VBRKA
                  (@P0.H_parser_inst.fuzz_one_P0_closed (guardP dA) (ceilP spA VSPA))) as RA.
    destruct (realizes_run_fields _ _ _ _ _ _ _ _ _ _ RA) as [EA TA].
    pose proof (a0_realizes_P0_shape (ceilP spA VSPA) inp spA brkA mbA dA (mkEntry spB brkB mbB dB) VI VA0 VB0 (ceilP_eq spA VSPA)
                  (realizes_has_nil _ _ _ RA)) as RB.
    unfold strong_equiv_error_free_scfg, error_free. cbn [run_scfg imgP0 imgA0 bh_errors bh_traces].
    split; [exact EA|]. split; [exact (SRZ_no_error asegs _ _ RB)|].
    intros tr. rewrite (TA tr). symmetry. exact (SRZ_obs_iff asegs _ _ RB tr).
  Qed.
End HandOff.

Check (fuzzhttp_asan_error_free_of
        : forall H_MAIN_A0 RS_A SRZ, _ -> _ -> _ -> _ -> HANDOFF H_MAIN_A0 SRZ -> MAIN H_MAIN_A0 RS_A -> SHAPE H_MAIN_A0 RS_A ->
          strong_universal_error_free_T_scfg ACFG
            (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
            (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs)).

