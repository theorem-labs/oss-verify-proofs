(* NEGATIVE CONTROL: a lemma of the wrong type.  It proves the premises of
   agreement_decidable on the instance's finite input, which leave out that
   its AT_HWCAP word is RV64GC's, under the name
   asan_agreement_decidable_rv64gc_may_fail expects, whose shape
   agreement_decidable_rv64gc has that premise, so the wrapper does not
   type-check. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import FinInput.
From OSSVerify.Tests.proofs.lib Require Import EbreakInstance.
From OSSVerify.Tests.toy.ebreak Require Images.

Lemma asan_agreement_decidable_rv64gc_may_fail_instance :
  valid_fin_input (fin_input reaches_harness seven)
  /\ (exists ep es, valid_entry Images.plain ep (to_proc_input (fin_input reaches_harness seven))
                    /\ valid_entry Images.asan es (to_proc_input (fin_input reaches_harness seven))).
Proof. exact (fin_premises _ _ launch_argv_reaches_harness). Qed.
