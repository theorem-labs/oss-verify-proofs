(* NEGATIVE CONTROL: a lemma of the wrong type.  It proves the premises of
   disagrees_at_most_rv64gc on the instance's finite input, which add that
   its AT_HWCAP word is RV64GC's, under the name
   asan_disagrees_at_most_may_fail expects, whose shape disagrees_at_most
   has no such premise, so the wrapper does not type-check. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import FinInput.
From OSSVerify.Tests.proofs.lib Require Import EbreakInstance.
From OSSVerify.Tests.toy.ebreak Require Images.

Lemma asan_disagrees_at_most_may_fail_instance :
  valid_fin_input (fin_input reaches_harness seven)
  /\ in_hwcap (to_proc_input (fin_input reaches_harness seven)) = hwcap_rv64gc
  /\ (exists ep es, valid_entry Images.plain ep (to_proc_input (fin_input reaches_harness seven))
                    /\ valid_entry Images.asan es (to_proc_input (fin_input reaches_harness seven))).
Proof. exact (fin_premises_rv64gc _ _ launch_argv_reaches_harness). Qed.
