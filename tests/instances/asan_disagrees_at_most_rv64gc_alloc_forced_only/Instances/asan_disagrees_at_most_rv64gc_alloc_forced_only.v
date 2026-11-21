(** POSITIVE CONTROL: the instance of
    toy/ebreak/asan_disagrees_at_most_rv64gc_alloc_forced_only, of the shape
    [disagrees_at_most_rv64gc].  Its file, wrong-argc.bin, is empty, and its
    path is refused-by-driver: argv is ["ebreak"].  The instance is a finite
    input, the one a Distribution.v builds over the file system
    [("input.bin", [])] with an empty file.  It is valid, its AT_HWCAP word
    is RV64GC's, and both builds have a valid entry on it. *)
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import FinInput.
From OSSVerify.Tests.proofs.lib Require Import EbreakInstance.
From OSSVerify.Tests.toy.ebreak Require Images.
Import ListNotations.

Lemma asan_disagrees_at_most_rv64gc_alloc_forced_only_instance :
  valid_fin_input (fin_input refused_by_driver [])
  /\ in_hwcap (to_proc_input (fin_input refused_by_driver [])) = hwcap_rv64gc
  /\ (exists ep es, valid_entry Images.plain ep (to_proc_input (fin_input refused_by_driver []))
                    /\ valid_entry Images.asan es (to_proc_input (fin_input refused_by_driver []))).
Proof. exact (fin_premises_rv64gc _ _ launch_argv_refused_by_driver). Qed.
