(* NEGATIVE CONTROL: a lemma of the wrong type.  It proves the premises of
   agrees on the instance's input, whose budget premise is over the
   unconfigured run, under the name asan_agrees_in_asan expects, whose shape
   agrees_in has its budget premise over the run under Env.alloc_forced_only
   (run_scfg), so the wrapper does not type-check. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.proofs.lib Require Import EbreakInstance.
From OSSVerify.Tests.toy.ebreak Require Images.

Lemma asan_agrees_in_asan_instance :
  exists ep es, valid_entry Images.plain ep (input false reaches_harness seven)
    /\ valid_entry Images.asan es (input false reaches_harness seven)
    /\ valid_input (input false reaches_harness seven)
    /\ ~ run_budget_refused Images.plain Budgets.Asan.lim_source ep (input false reaches_harness seven).
Proof. exact (agrees_premises _ _ _ launch_argv_reaches_harness). Qed.
