(* NEGATIVE CONTROL: a lemma that is not finished.  [Admitted] makes it an
   axiom, which is not in toolchain/allowed-axioms.txt. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.exit0 Require Images.
From OSSVerify.Tests.proofs.lib Require Import Exit0Instance.

Lemma plain_halts_instance :
  exists en, valid_entry Images.plain en (input reaches_harness seven)
    /\ valid_input (input reaches_harness seven)
    /\ ~ run_scfg_budget_refused forced_only_cfg Images.plain Budgets.Standard.lim_source en
           (input reaches_harness seven).
Admitted.
