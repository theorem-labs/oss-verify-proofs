(** Connect the reused symbolic executor to the original halting predicate.
    No execution semantics or process model is replaced. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
  YK11 YK0i YP02 YP0m YP09 YP0l YP0k YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib Require Import Startup StartupExit.

Lemma msteps_as_pure_steps : forall segs ms final,
  msteps segs ms final -> exists n, pure_steps segs n ms final.
Proof.
  intros segs ms final H.
  induction H as [ms | ms mid final Hsvc Hstep Htail [n IH]].
  - exists 0%nat. constructor.
  - exists (S n). econstructor; eassumption.
Qed.

Lemma msteps_preserve_must_exit : forall segs ms final,
  msteps segs ms final -> forall cfg allowed model,
  m_halted model = None -> m_vm_lazy model = nil ->
  must_exit_in_at_cfg cfg segs allowed (mkCfg final model) ->
  must_exit_in_at_cfg cfg segs allowed (mkCfg ms model).
Proof.
  intros segs ms final H cfg allowed model Hh Hl Hexit.
  destruct (msteps_as_pure_steps segs ms final H) as [n Hp].
  eapply pure_steps_preserve_must_exit; eassumption.
Qed.

Section Symbolic.
  Context {fx : FPState}.
  Variables (segs : list Segment) (tbl : ctable).
  Hypothesis Htbl : table_ok segs tbl.

  Theorem symbolic_run_preserves_must_exit : forall n E ss ss' st ms cfg allowed model,
    st_ok segs E ss ms ->
    sym_runN segs tbl n ss = (ss', st) ->
    m_halted model = None -> m_vm_lazy model = nil ->
    (forall final,
      (match st with RS_ecall => st_ok_ecall segs E ss' final
                     | _ => st_ok segs E ss' final end) ->
      frame_of E (ss_mem ss) (ms_mem ms) (ms_mem final) ->
      must_exit_in_at_cfg cfg segs allowed (mkCfg final model)) ->
    must_exit_in_at_cfg cfg segs allowed (mkCfg ms model).
  Proof.
    intros n E ss ss' st ms cfg allowed model HS HR Hh Hl K.
    destruct (msteps_run_gen segs tbl Htbl n E ss ss' st ms HS HR)
      as [final [Hsteps [HS' Hframe]]].
    eapply msteps_preserve_must_exit; [exact Hsteps | exact Hh | exact Hl |].
    apply K; assumption.
  Qed.
End Symbolic.

Set Printing Fully Qualified.
Print Assumptions symbolic_run_preserves_must_exit.
