(* NEGATIVE CONTROL: a lemma of the wrong type.  It proves the premises of
   agrees_abort_modelled on the instance's input, whose budget premise is
   over the unconfigured run, under the name
   asan_agrees_in_abort_modelled_standard expects, whose shape
   agrees_in_abort_modelled has its budget premise over the run under
   Env.alloc_forced_only (run_scfg), so the wrapper does not type-check. *)
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.proofs.lib Require Import EbreakInstance.
From OSSVerify.Tests.toy.ebreak Require Images.
Import ListNotations.

Lemma asan_agrees_in_abort_modelled_standard_instance :
  exists ep es, valid_entry Images.plain ep (input true refused_by_driver [])
    /\ valid_entry Images.asan es (input true refused_by_driver [])
    /\ valid_input_abort (input true refused_by_driver [])
    /\ ~ run_budget_refused Images.plain Budgets.Standard.lim_source ep (input true refused_by_driver []).
Proof. exact (agrees_abort_modelled_premises _ _ _ launch_argv_refused_by_driver). Qed.
