(** POSITIVE CONTROL: the instance of toy/exit0/plain_halts.  Its file,
    input.bin, holds the 7 bytes [Exit0Instance.seven], and its path is
    reaches-harness: argv is ["exit0"; "input.bin"].  On that input the
    premises of [halts_within_budget] hold together: a valid entry, a valid
    input, and a run that is never refused memory. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.exit0 Require Images.
From OSSVerify.Tests.proofs.lib Require Import Exit0Instance.

Lemma plain_halts_instance :
  exists en, valid_entry Images.plain en (input reaches_harness seven)
    /\ valid_input (input reaches_harness seven)
    /\ ~ run_scfg_budget_refused forced_only_cfg Images.plain Budgets.Standard.lim_source en
           (input reaches_harness seven).
Proof. exact (halts_within_budget_premises _ _ launch_argv_reaches_harness). Qed.
