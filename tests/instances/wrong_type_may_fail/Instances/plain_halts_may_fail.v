(* NEGATIVE CONTROL: a lemma of the wrong type.  It proves the premises of
   halts_within_budget on the instance's input, which add the budget premise,
   under the name plain_halts_may_fail expects, whose shape halts_may_fail
   has no budget premise, so the wrapper does not type-check. *)
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.exit0 Require Images.
From OSSVerify.Tests.proofs.lib Require Import Exit0Instance.
Import ListNotations.

Lemma plain_halts_may_fail_instance :
  exists en, valid_entry Images.plain en (input refused_by_driver [])
    /\ valid_input (input refused_by_driver [])
    /\ ~ run_scfg_budget_refused forced_only_cfg Images.plain Budgets.Standard.lim_source en
           (input refused_by_driver []).
Proof. exact (halts_within_budget_premises _ _ launch_argv_refused_by_driver). Qed.
