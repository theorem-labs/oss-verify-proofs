(* NEGATIVE CONTROL: a lemma of the wrong type.  It proves the premises of
   agreement_decidable_rv64gc on the instance's finite input, which add that
   its AT_HWCAP word is RV64GC's, under the name
   asan_agreement_decidable_alloc_forced_only expects, whose shape
   agreement_decidable has no such premise, so the wrapper does not
   type-check. *)
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import FinInput.
From OSSVerify.Tests.proofs.lib Require Import EbreakInstance.
From OSSVerify.Tests.toy.ebreak Require Images.
Import ListNotations.

Lemma asan_agreement_decidable_alloc_forced_only_instance :
  valid_fin_input (fin_input refused_by_driver [])
  /\ in_hwcap (to_proc_input (fin_input refused_by_driver [])) = hwcap_rv64gc
  /\ (exists ep es, valid_entry Images.plain ep (to_proc_input (fin_input refused_by_driver []))
                    /\ valid_entry Images.asan es (to_proc_input (fin_input refused_by_driver []))).
Proof. exact (fin_premises_rv64gc _ _ launch_argv_refused_by_driver). Qed.
