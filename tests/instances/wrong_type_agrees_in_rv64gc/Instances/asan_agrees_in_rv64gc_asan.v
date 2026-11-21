(* NEGATIVE CONTROL: a lemma of the wrong type.  It proves the premises of
   agrees_in on the instance's input, whose input predicate valid_input
   allows either AT_HWCAP word, under the name asan_agrees_in_rv64gc_asan
   expects, whose shape agrees_in_rv64gc reads valid_input_hwcap_rv64gc, so
   the wrapper does not type-check. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.proofs.lib Require Import EbreakInstance.
From OSSVerify.Tests.toy.ebreak Require Images.

Lemma asan_agrees_in_rv64gc_asan_instance :
  exists ep es, valid_entry Images.plain ep (input false reaches_harness seven)
    /\ valid_entry Images.asan es (input false reaches_harness seven)
    /\ valid_input (input false reaches_harness seven)
    /\ ~ run_scfg_budget_refused Env.alloc_forced_only Images.plain Budgets.Asan.lim_source ep
           (input false reaches_harness seven).
Proof. exact (agrees_in_premises _ _ _ _ launch_argv_reaches_harness). Qed.
