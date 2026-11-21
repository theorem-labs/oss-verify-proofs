(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(** * Common.ErrEscape — the SOURCE-ERROR ESCAPE glue.

    TRUST BOUNDARY: image-INDEPENDENT proof library (like Common.ExitSim),
    NOT part of the trusted specification.

    Following the PropExec conventions: the decode hypotheses go through
    [DecodeC.decode_any] with [Instr] [Load] ASTs and encoded-width
    [bv 12] immediates; the faulting address is
    [v_addi (getr regs rs) (bv_signed imm)] (the [step_lbu]/[step_ld]
    address shape), read via [ov_rdn].  The instruction SIZE returned by
    [decode_any] is quantified ([isz : Z], where the healthy load lemmas pin [4%Z]) —
    a faulting load never advances the pc, so the same lemma covers a
    compressed [C.LD] encoding.

    [Equivalence.equiv] contains an escape hatch only if EVERY execution
    of the SOURCE binary reaches the explicit error transition.  This
    file packages that proof for the most common all-error shape: a
    deterministic straight line of ordinary instructions ending in an
    illegal one (e.g. a load from an unmapped address):

    - [step_lbu_fault] / [step_ld_fault]: a byte/double load whose
      address is unreadable (writable overlay AND ROM both miss) is an
      illegal instruction ([MachineFault]);
    - [msteps_illegal_all_traces_error]: an [msteps] run
      (Common.CatSim) into a non-syscall state whose next step is
      [MachineFault] proves [Run.all_traces_error];
    - [err_escape_equiv]: at the [Equivalence] level, such a source run
      discharges [equiv (run source ...) target] for ANY [target]
      behavior — the target need not be analyzed at all.

    The omni reading ([msteps_illegal_exec]) says the same in ONE
    judgment: every execution of the path ends by erroring FROM the
    faulting configuration.  [OmniRun.exec] with that postcondition
    carries both what the escape needs ([Run.all_traces_error], via
    [OmniRun.all_traces_error_iff]) and what keeps the escape honest
    ([Equivalence.modeled], via [OmniRun.coexec_covered] and the fact
    that a [MachineFault] is not the model giving up), so the two
    sections below are corollaries of it, and [err_escape_omni_strong_equiv]
    is the packaged escape in the shape of
    [OmniEquivalence.omni_strong_equiv]. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import ExitSim PropExec CatSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* ================================================================= *)
(* Faulting loads                                                    *)
(* ================================================================= *)

(** A byte load from an unreadable address is an illegal instruction.

    THE vvar PREMISE IS NOT A WEAKENING, it is the vDSO's own rule: the
    four vvar pages are readable on Linux and the model has no term for
    their contents, so a load that MEETS them is
    [RiscvSemantics.MachineUnmodeled] — the model declining — rather
    than the fault an unmapped address gives
    ([RiscvSemantics.range_meets_vvar], and SCOPE.md's "The vDSO").
    Without the premise this lemma is false at any segment list that
    carries the pair.  Every caller supplies a binary's own segments,
    where it is [reflexivity]. *)
Lemma step_lbu_fault : forall segs regs pc mem rom w rd rs (imm : bv 12) (isz : Z),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ1 false rd rs imm, isz) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = None ->
  range_meets_vvar segs (v_addi (getr regs rs) (bv_signed imm)) 1%nat = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineFault.
Proof.
  intros segs regs pc mem rom w rd rs imm isz Hfetch Hecall Hdecode Hread Hvv.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hread, Hvv; rewrite ?bv_eqb0_is_x0 in Hread, Hvv.
  rewrite ov_rdn, b_addsext, Hread, Hvv.
  reflexivity.
Qed.

(** A double load from an unreadable address is an illegal instruction;
    the vvar premise is [step_lbu_fault]'s. *)
Lemma step_ld_fault : forall segs regs pc mem rom w rd rs (imm : bv 12) (isz : Z),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ8 true rd rs imm, isz) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8%nat = None ->
  range_meets_vvar segs (v_addi (getr regs rs) (bv_signed imm)) 8%nat = false ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineFault.
Proof.
  intros segs regs pc mem rom w rd rs imm isz Hfetch Hecall Hdecode Hread Hvv.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr in Hread, Hvv; rewrite ?bv_eqb0_is_x0 in Hread, Hvv.
  rewrite ov_rdn, b_addsext, Hread, Hvv.
  reflexivity.
Qed.

(* ================================================================= *)
(* msteps into an illegal step reaches the error transition          *)
(* ================================================================= *)

Section WithSegs.
Variable segs : list Segment.

(** An [msteps] run is a silent [star] (the model is untouched). *)
Lemma msteps_star_nil : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  star segs (mkCfg ms model) [] (mkCfg ms' model).
Proof.
  intros ms ms' model Hh Hlazy H.
  induction H as [ms | ms ms1 ms2 Hsvc Hstep H IH].
  - apply star_refl.
  - change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [| exact IH].
    apply (sstep_instr segs ms model ms1 model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

(** Straight line of instructions, then an illegal one: error reached. *)
Lemma msteps_illegal_error : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  reaches_error segs (mkCfg ms model).
Proof.
  intros ms ms' model Hh Hlazy Hm Hsvc Hill.
  exists [], (mkCfg ms' model), [].
  split; [apply msteps_star_nil; assumption |].
  apply sstep_instr_fault; [assumption | assumption |].
  rewrite (mi_account_step_no_lazy segs ms' model Hlazy), Hill. reflexivity.
Qed.

End WithSegs.

(* ================================================================= *)
(* The omni reading: one judgment for the whole escape               *)
(* ================================================================= *)

Section OmniWithSegs.
Variable segs : list Segment.

(** The faulting state: its only transition is the error one, taken
    from itself. *)
Lemma illegal_exec : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineFault ->
  OmniRun.exec segs (mkCfg ms model) (fun tr o => tr = [] /\ o = OError (mkCfg ms model)).
Proof.
  intros ms model Hh Hlazy Hsvc Hill.
  apply exec_step; [exact Hh | | |].
  - exists [], SError. apply sstep_instr_fault; [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill. reflexivity.
  - intros evs Hss. inversion Hss; subst; split; reflexivity.
  - intros evs c' Hnext. exfalso. inversion Hnext; subst; try congruence;
    (* the vDSO arms carry [MachineUnmodeled] where this state is
       [MachineFault], so they close the same way the ordinary
       instruction arm does *)
    match goal with H : mi_account_step segs ms model = _ |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill in H;
      discriminate
    end.
Qed.

(** One ordinary instruction in front of any omni judgment: the
    transition is unique and silent, so the postcondition is unchanged. *)
Lemma instr_exec : forall ms ms' model (Q : post),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  OmniRun.exec segs (mkCfg ms' model) Q ->
  OmniRun.exec segs (mkCfg ms model) Q.
Proof.
  intros ms ms' model Q Hh Hlazy Hsvc Hstep Hex.
  apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
  - apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - intros evs st Hss.
    exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
  - eapply exec_conseq; [exact Hex |]. intros tr o H. cbn [app]. exact H.
Qed.

Lemma msteps_exec : forall ms ms' model (Q : post),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  OmniRun.exec segs (mkCfg ms' model) Q ->
  OmniRun.exec segs (mkCfg ms model) Q.
Proof.
  intros ms ms' model Q Hh Hlazy Hm Hex.
  induction Hm as [ms0 | ms0 ms1 ms2 Hsvc Hstep Htail IH]; [exact Hex |].
  eapply instr_exec; eauto.
Qed.

(** THE judgment: a deterministic instruction path ending in an illegal
    instruction errors, on every execution, from that instruction's
    configuration. *)
Lemma msteps_illegal_exec : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  OmniRun.exec segs (mkCfg ms model) (fun tr o => tr = [] /\ o = OError (mkCfg ms' model)).
Proof.
  intros ms ms' model Hh Hlazy Hm Hsvc Hill.
  eapply msteps_exec; [exact Hh | exact Hlazy | exact Hm |].
  apply illegal_exec; assumption.
Qed.

(** The faulting configuration is covered: the fault is a
    [MachineFault], not the model giving up. *)
Lemma fault_covered_at : forall ms model,
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineFault ->
  ~ unmodeled_at segs (mkCfg ms model).
Proof.
  intros ms model Hlazy Hsvc Hfault
    (_ & [(_ & Hum & _) | [(_ & Hum & _) | (x8 & Hsvc' & _)]]); cbn in *.
  - rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in Hum.
    discriminate.
  - (* the vDSO shape: same [MachineUnmodeled] against this fault *)
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in Hum.
    discriminate.
  - congruence.
Qed.

(** What the one judgment yields: the escape ... *)
Lemma msteps_illegal_errors : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  OmniRun.exec segs (mkCfg ms model) errors.
Proof.
  intros ms ms' model Hh Hlazy Hm Hsvc Hill.
  eapply exec_conseq; [eapply msteps_illegal_exec; eassumption |].
  intros tr o (_ & ->). exact I.
Qed.

(** ... and coverage, without a separate walk of the path. *)
Lemma msteps_illegal_covered : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  OmniRun.coexec segs (mkCfg ms model) (covered segs).
Proof.
  intros ms ms' model Hh Hlazy Hm Hsvc Hill.
  apply exec_coexec.
  eapply exec_conseq; [eapply msteps_illegal_exec; eassumption |].
  intros tr o (_ & ->). unfold covered. apply fault_covered_at; assumption.
Qed.

(** Bites: the judgment NAMES the outcome, so the other readings of the
    same path are refuted — it does not exit with any code, and it is not
    error-free. *)
Lemma msteps_illegal_no_exit : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  forall code, ~ OmniRun.exec segs (mkCfg ms model) (exits_with code).
Proof.
  intros ms ms' model Hh Hlazy Hm Hsvc Hill code Hex.
  destruct (exec_realizes _ _ _ (msteps_illegal_exec _ _ _ Hh Hlazy Hm Hsvc Hill))
    as (tr & o & Hm' & _ & ->).
  exact (exec_sound _ _ _ Hex _ _ Hm').
Qed.

Lemma msteps_illegal_not_never_errors : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  ~ OmniRun.coexec segs (mkCfg ms model) never_errors.
Proof.
  intros ms ms' model Hh Hlazy Hm Hsvc Hill Hco.
  destruct (exec_realizes _ _ _ (msteps_illegal_exec _ _ _ Hh Hlazy Hm Hsvc Hill))
    as (tr & o & Hm' & _ & ->).
  exact (coexec_sound _ _ _ _ Hm' _ Hco I).
Qed.

End OmniWithSegs.

(* ================================================================= *)
(* Universal error for deterministic instruction paths               *)
(* ================================================================= *)

Section AllErrorWithSegs.
Variable segs : list Segment.

(** An illegal ordinary-instruction state has exactly the error step and
    therefore all of its executions error. *)
Lemma illegal_all_traces_error : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineFault ->
  all_traces_error segs (mkCfg ms model).
Proof.
  intros ms model Hh Hlazy Hsvc Hill.
  constructor.
  - exists [], SError. apply sstep_instr_fault; [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill. reflexivity.
  - intros evs c' Hnext. inversion Hnext; subst; try congruence;
    match goal with H : mi_account_step segs ms model = _ |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hill in H;
      discriminate
    end.
Qed.

(** Prepending the unique ordinary instruction transition preserves the
    universal error property. *)
Lemma instr_all_traces_error : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  all_traces_error segs (mkCfg ms' model) ->
  all_traces_error segs (mkCfg ms model).
Proof.
  intros ms ms' model Hh Hlazy Hsvc Hstep Hall.
  constructor.
  - exists [], (SNext (mkCfg ms' model)).
    apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
  - intros evs c' Hnext.
    destruct (sstep_instr_inv segs ms model ms' evs (SNext c')
                Hlazy Hsvc Hstep Hnext) as [_ Hto].
    inversion Hto; subst. exact Hall.
Qed.

(** Prepend any deterministic sequence of ordinary instructions to an
    all-error configuration. *)
Lemma msteps_all_traces_error : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  all_traces_error segs (mkCfg ms' model) ->
  all_traces_error segs (mkCfg ms model).
Proof.
  intros ms ms' model Hh Hlazy Hm Hall.
  induction Hm as [ms0 | ms0 ms1 ms2 Hsvc Hstep Htail IH].
  - exact Hall.
  - eapply instr_all_traces_error; eauto.
Qed.

(** A deterministic instruction path ending in an illegal instruction
    has no alternative non-error trace. *)
Lemma msteps_illegal_all_traces_error : forall ms ms' model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  all_traces_error segs (mkCfg ms model).
Proof.
  intros ms ms' model Hh Hlazy Hm Hfinal_svc Hillegal.
  apply all_traces_error_iff. eapply msteps_illegal_errors; eassumption.
Qed.

End AllErrorWithSegs.

(* ================================================================= *)
(* Coverage: the deterministic fault path is MODELED                 *)
(* ================================================================= *)

(** The escape paths are exactly the paths where the source is EXPECTED
    to error, so they are the paths where [Equivalence.modeled] cannot be
    obtained from a [~ reaches_error] proof (there is no such proof —
    the source really does error).  They have to be closed directly, and
    the content of doing so is the whole point of the split: the fault at
    the end of the path is a [MachineFault] — a load from an unmapped
    address, which a real process suffers as SIGSEGV — and every state
    before it is an ordinary [MachineOk] instruction.  Nowhere on the
    path does the MODEL give up, so the run is fully covered even though
    it dies. *)

Section NoUnmodeledWithSegs.
Variable segs : list Segment.

(** A configuration with no [SNext] successor is only [star]-reachable
    from itself. *)
Lemma star_stuck_refl : forall c tr c',
  (forall evs c2, ~ sstep segs c evs (SNext c2)) ->
  star segs c tr c' -> c' = c.
Proof.
  intros c tr c' Hno Hstar. inversion Hstar; subst; [reflexivity|].
  exfalso. eapply Hno; eassumption.
Qed.

(** The faulting state itself is covered: its only transition is the
    error one, and that error is a genuine fault. *)
Lemma fault_no_unmodeled : forall ms model,
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineFault ->
  ~ reaches_unmodeled segs (mkCfg ms model).
Proof.
  intros ms model Hlazy Hsvc Hfault (tr & c & Hstar & Hun).
  assert (Hno : forall evs c2, ~ sstep segs (mkCfg ms model) evs (SNext c2)).
  { intros evs c2 Hss. inversion Hss; subst; try congruence;
    match goal with H : mi_account_step segs ms model = _ |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in H;
      discriminate
    end. }
  rewrite (star_stuck_refl _ tr c Hno Hstar) in Hun.
  destruct Hun as (_ & [(_ & Hum & _) | [(_ & Hum & _) | (x8 & Hsvc' & _)]]);
    cbn in *.
  - rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in Hum.
    discriminate.
  - rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hfault in Hum.
    discriminate.
  - congruence.
Qed.

(** One ordinary instruction in front of a covered configuration. *)
Lemma instr_no_unmodeled : forall ms ms' model,
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  ~ reaches_unmodeled segs (mkCfg ms' model) ->
  ~ reaches_unmodeled segs (mkCfg ms model).
Proof.
  intros ms ms' model Hlazy Hsvc Hstep Hnext (tr & c & Hstar & Hun).
  inversion Hstar as [| c1 evs c2 tr2 c3 Hss Hrest]; subst.
  - destruct Hun as (_ & [(_ & Hum & _) | [(_ & Hum & _) | (x8 & Hsvc' & _)]]);
      cbn in *.
    + rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep in Hum.
      discriminate.
    + rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep in Hum.
      discriminate.
    + congruence.
  - destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
                Hlazy Hsvc Hstep Hss)
      as [_ Hc2].
    inversion Hc2; subst. apply Hnext. exists tr2, c. split; assumption.
Qed.

(** A deterministic instruction path ending in a genuine fault never
    reaches a configuration the model does not cover. *)
Lemma msteps_fault_no_unmodeled : forall ms ms' model,
  msteps segs ms ms' ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step segs ms' = MachineFault ->
  ~ reaches_unmodeled segs (mkCfg ms model).
Proof.
  intros ms ms' model Hm Hlazy Hsvc Hfault.
  destruct (m_halted model) as [code |] eqn:Hh.
  - (* a halted model takes no transition, and a halted configuration is
       not one the model declined *)
    intros (tr & c & Hstar & Hun).
    inversion Hstar as [| c1 evs c2 tr2 c3 Hss]; subst.
    + destruct Hun as (Hun & _). cbn in Hun. congruence.
    + pose proof (sstep_from_running segs _ _ _ Hss) as Hrun. cbn in Hrun. congruence.
  - apply coexec_covered. eapply msteps_illegal_covered; eassumption.
Qed.

End NoUnmodeledWithSegs.

(* ================================================================= *)
(* Equivalence-level escape                                          *)
(* ================================================================= *)

(** The omni escape, per run: the source's judgment at any budget ... *)
Lemma err_escape_omni_run :
  forall segs pc ph sp brk0 mb rnd lim inp ms',
  msteps (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step (run_segments segs inp sp mb) ms' = MachineFault ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp errors.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
  cbn [omni_run]. unfold init_config.
  eapply msteps_illegal_errors; [reflexivity | reflexivity | exact Hm | exact Hsvc | exact Hill].
Qed.

(** ... its coverage ... *)
Lemma err_escape_omni_covered :
  forall segs pc ph sp brk0 mb rnd lim inp ms',
  msteps (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step (run_segments segs inp sp mb) ms' = MachineFault ->
  omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (covered (run_segments segs inp sp mb)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
  cbn [omni_corun]. unfold init_config.
  eapply msteps_illegal_covered; [reflexivity | reflexivity | exact Hm | exact Hsvc | exact Hill].
Qed.

(** ... [OmniEquivalence.omni_equiv] against ANY target run ... *)
Lemma err_escape_omni_equiv :
  forall segs pc ph sp brk0 mb rnd lim inp T limT et ms',
  msteps (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step (run_segments segs inp sp mb) ms' = MachineFault ->
  omni_equiv (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) T limT et inp.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp T limT et ms' Hm Hsvc Hill.
  left. eapply err_escape_omni_run; eassumption.
Qed.

(** ... and the packaged [OmniEquivalence.omni_strong_equiv]: a source
    that deterministically faults, against any target image and entry. *)
Lemma err_escape_omni_strong_equiv :
  forall segs pc ph sp brk0 mb rnd inp T et ms',
  msteps (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step (run_segments segs inp sp mb) ms' = MachineFault ->
  omni_strong_equiv (mkImage segs pc ph) T (mkEntry sp brk0 mb rnd) et inp.
Proof.
  intros segs pc ph sp brk0 mb rnd inp T et ms' Hm Hsvc Hill.
  split.
  - cbn [img_segments]. eapply err_escape_omni_covered; eassumption.
  - eapply err_escape_omni_equiv; eassumption.
Qed.

(** If the SOURCE deterministically runs into a faulting instruction,
    [equiv] holds against ANY target behavior (the escape in
    [Equivalence.equiv]): the target is freed entirely.  From the omni
    judgment through [OmniRun.bh_all_errors_iff]. *)
Lemma err_escape_equiv :
  forall segs pc ph sp brk0 mb rnd lim inp (target : behavior) ms',
  msteps (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step (run_segments segs inp sp mb) ms' = MachineFault ->
  Equivalence.equiv (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) target.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp target ms' Hm Hsvc Hill.
  left. apply bh_all_errors_iff. eapply err_escape_omni_run; eassumption.
Qed.

(** …and the same run is MODELED: it dies, but at a [MachineFault], with
    nothing but ordinary instructions before it.  This is what stops the
    escape from being a way to launder an unmodeled source through the
    theorem.  From the same omni judgment, through
    [OmniEquivalence.modeled_iff]. *)
Lemma err_escape_modeled :
  forall segs pc ph sp brk0 mb rnd lim inp ms',
  msteps (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step (run_segments segs inp sp mb) ms' = MachineFault ->
  Equivalence.modeled (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp ms' Hm Hsvc Hill.
  apply modeled_iff. cbn [img_segments]. eapply err_escape_omni_covered; eassumption.
Qed.

(** The packaged escape: both clauses of [Equivalence.strong_equiv] for a
    source that deterministically faults, against ANY target. *)
Lemma err_escape_strong_equiv :
  forall segs pc ph sp brk0 mb rnd lim inp (target : behavior) ms',
  msteps (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ms' ->
  ms_svc_pending ms' = None ->
  RiscvSemantics.step (run_segments segs inp sp mb) ms' = MachineFault ->
  Equivalence.modeled (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp)
  /\ Equivalence.equiv (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp)
       target.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp target ms' Hm Hsvc Hill.
  split; [eapply err_escape_modeled | eapply err_escape_equiv]; eassumption.
Qed.
End WithFP1.
