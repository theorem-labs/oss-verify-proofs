(** Transport a halting obligation across a checked pure-instruction prefix.
    The instruction case follows the proof pattern of the pinned LPS lemma
    Checks.SpuriousCfg.exits_c_must_exit_at_cfg. All transitions and accounting
    are those of LPS; this introduces no execution or syscall semantics. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib Require Import Startup.

Lemma pure_steps_preserve_must_exit : forall segs n ms final,
  pure_steps segs n ms final -> forall cfg allowed model,
  m_halted model = None -> m_vm_lazy model = nil ->
  must_exit_in_at_cfg cfg segs allowed (mkCfg final model) ->
  must_exit_in_at_cfg cfg segs allowed (mkCfg ms model).
Proof.
  intros segs n ms final Hp.
  induction Hp as [ms|n ms mid final Hsvc Hstep Htail IH];
    intros cfg allowed model Hh Hlazy Hexit.
  - exact Hexit.
  - assert (Hacc : mi_account_step segs ms model = MachineOk (mid, model)).
    { rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity. }
    apply must_exit_in_at_cfg_running.
    + cbn [cfg_model]. exact Hh.
    + exists nil, (SNext (mkCfg mid model)).
      eapply sstep_cfg_instr; eassumption.
    + intros evs Hss. inversion Hss; subst; congruence.
    + intros evs c' Hss. inversion Hss; subst; try congruence.
      match goal with
      | [ H : mi_account_step _ _ _ = MachineOk (?a, ?b) |- _ ] =>
          rewrite Hacc in H; injection H as -> ->
      end.
      apply IH; assumption.
Qed.

Set Printing Fully Qualified.
Print Assumptions pure_steps_preserve_must_exit.
