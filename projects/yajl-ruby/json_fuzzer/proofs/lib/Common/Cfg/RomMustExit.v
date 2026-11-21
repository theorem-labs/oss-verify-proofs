(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 08b1429): [RomStable.run_init] for [MustExit.must_exit_at_cfg].

   [must_exit_with_scfg] runs a binary over [run_segments segs inp sp mb] from the run's own start
   [init_config (run_segments ..) ..].  A must-exit walk over the binary's own segments from the
   binary's start lifts to it the way a [realizes_cfg] walk does ([RomStable.run_init]), when
   each running state's system call, if any, reads the same input over a larger read-only
   backing ([RomBase.sys_rob]).  [me_rob] is [must_exit_at_cfg] with that fact at each running
   state; [must_exit_run_init] is the lift. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common.Cfg Require Import RomBase RomStable.
Import ListNotations.

Inductive me_rob (cfg : SpuriousCfg) (segs : list Segment) (code : word) : config -> Prop :=
| mer_halted : forall c,
    m_halted (cfg_model c) = Some code ->
    m_killed (cfg_model c) = None ->
    me_rob cfg segs code c
| mer_running : forall c,
    m_halted (cfg_model c) = None ->
    sys_rob segs c ->
    (exists evs st, sstep_cfg segs cfg c evs st) ->
    (forall evs, ~ sstep_cfg segs cfg c evs SError) ->
    (forall evs c', sstep_cfg segs cfg c evs (SNext c') -> me_rob cfg segs code c') ->
    me_rob cfg segs code c.

Lemma me_rob_must_exit : forall cfg segs code c, me_rob cfg segs code c -> must_exit_at_cfg cfg segs code c.
Proof.
  intros cfg segs code c H.
  induction H as [c Hh Hk | c Hh Hrob Hprog Hnoerr Hnext IH].
  - apply must_exit_at_cfg_halted; assumption.
  - apply must_exit_at_cfg_running; [exact Hh | exact Hprog | exact Hnoerr | exact IH].
Qed.

Section Wrom.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable code : word.
Hypothesis Hvi : vdso_image segs = None.

Theorem me_rob_wrom : forall c, me_rob cfg segs code c ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> me_rob cfg segs code (cwrom c r).
Proof.
  intros c H. induction H as [c Hh Hk | c Hh Hrob Hprog Hnoerr Hnext IH]; intros r Hr.
  - apply mer_halted; [exact Hh | exact Hk].
  - apply mer_running.
    + exact Hh.
    + exact (sys_rob_wrom segs c r Hrob Hr).
    + destruct Hprog as (evs & st & Hss). destruct st as [c'|]; [| exfalso; exact (Hnoerr evs Hss)].
      exists evs, (SNext (cwrom c' r)). exact (sstep_wrom_fwd segs cfg Hvi c evs c' r Hrob Hr Hss).
    + intros evs Hss.
      destruct (sstep_wrom_back segs cfg Hvi c evs SError r Hrob Hr Hss) as (st0 & H0 & E).
      destruct st0 as [c0|]; [discriminate E | exact (Hnoerr evs H0)].
    + intros evs c2 Hss.
      destruct (sstep_wrom_back segs cfg Hvi c evs (SNext c2) r Hrob Hr Hss) as (st0 & H0 & E).
      destruct st0 as [c0|]; [| discriminate E]. injection E as ->.
      apply (IH evs c0 H0). rewrite (sstep_cfg_next_rom segs cfg Hvi c evs c0 H0). exact Hr.
Qed.
End Wrom.

Section AppTail.
Variables segs tail : list Segment.
Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
Hypothesis Hvi : vdso_image segs = None.
Variable cfg : SpuriousCfg.
Variable code : word.

Lemma vdso_entry_fn_none_tail : forall pc, vdso_entry_fn segs pc = None.
Proof. intros pc. unfold vdso_entry_fn. rewrite Hvi. reflexivity. Qed.

Theorem me_rob_app_tail : forall c, me_rob cfg segs code c -> me_rob cfg (segs ++ tail) code c.
Proof.
  intros c H. induction H as [c Hh Hk | c Hh Hrob Hprog Hnoerr Hnext IH].
  - apply mer_halted; [exact Hh | exact Hk].
  - destruct Hprog as (evs0 & st0 & Hss0).
    destruct st0 as [c0|]; [| exfalso; exact (Hnoerr evs0 Hss0)].
    destruct c as [ms model].
    assert (Hok : ms_svc_pending ms = None -> exists r, mi_account_step segs ms model = MachineOk r).
    { intros Hsvc. inversion Hss0; subst.
      - eexists. eassumption.
      - exfalso. rewrite vdso_entry_fn_none_tail in *. discriminate.
      - congruence.
      - congruence.
      - congruence. }
    apply mer_running.
    + exact Hh.
    + apply (sys_rob_app_tail segs tail); assumption.
    + exists evs0, (SNext c0). apply (sstep_cfg_app_next segs tail); assumption.
    + intros evs Hss. apply (Hnoerr evs).
      apply (sstep_cfg_app_back segs tail); assumption.
    + intros evs c2 Hss. apply (IH evs c2).
      apply (sstep_cfg_app_back segs tail); assumption.
Qed.
End AppTail.

Theorem me_rob_run_segments : forall cfg segs code inp (sp mb : word) c,
  vdso_image segs = None ->
  me_rob cfg segs code c -> me_rob cfg (run_segments segs inp sp mb) code c.
Proof.
  intros cfg segs code inp sp mb c Hvi H. unfold run_segments.
  apply me_rob_app_tail;
    [ intros s Hs; exact (vdso_segments_nx _ _ _ s Hs)
    | intros s Hs; exact (vdso_segments_nw _ _ _ s Hs)
    | exact Hvi | exact H ].
Qed.

(** A must-exit walk over the binary's own segments, from the binary's start, is one of the run. *)
Theorem must_exit_run_init : forall cfg segs code inp (sp mb : word) pc ph brk rnd lim,
  vdso_image segs = None ->
  me_rob cfg segs code (init_config segs pc ph sp brk mb rnd lim inp) ->
  must_exit_at_cfg cfg (run_segments segs inp sp mb) code
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp).
Proof.
  intros cfg segs code inp sp mb pc ph brk rnd lim Hvi H.
  rewrite init_config_run_segments.
  apply me_rob_must_exit, me_rob_run_segments; [exact Hvi|].
  apply (me_rob_wrom segs cfg code Hvi); [exact H|].
  rewrite init_config_rom. apply rom_ext_run_segments.
Qed.
