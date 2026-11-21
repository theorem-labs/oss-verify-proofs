(* NEGATIVE CONTROL: a lemma of the wrong type.  It proves the premises of
   disagrees_at_most on the instance's finite input, which leave out that
   its AT_HWCAP word is RV64GC's, under the name
   asan_disagrees_at_most_rv64gc_alloc_forced_only expects, whose shape
   disagrees_at_most_rv64gc has that premise, so the wrapper does not
   type-check. *)
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import FinInput.
From OSSVerify.Tests.proofs.lib Require Import EbreakInstance.
From OSSVerify.Tests.toy.ebreak Require Images.
Import ListNotations.

Lemma asan_disagrees_at_most_rv64gc_alloc_forced_only_instance :
  valid_fin_input (fin_input refused_by_driver [])
  /\ (exists ep es, valid_entry Images.plain ep (to_proc_input (fin_input refused_by_driver []))
                    /\ valid_entry Images.asan es (to_proc_input (fin_input refused_by_driver []))).
Proof. exact (fin_premises _ _ launch_argv_refused_by_driver). Qed.
