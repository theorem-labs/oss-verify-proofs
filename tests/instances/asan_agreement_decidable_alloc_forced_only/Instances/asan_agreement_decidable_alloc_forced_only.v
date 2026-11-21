(** POSITIVE CONTROL: the instance of
    toy/ebreak/asan_agreement_decidable_alloc_forced_only, of the shape
    [agreement_decidable].  Its file, wrong-argc.bin, is empty, and its path
    is refused-by-driver: argv is ["ebreak"].  The instance is a finite
    input, the one a Distribution.v builds over the file system
    [("input.bin", [])] with an empty file.  It is valid, and both builds
    have a valid entry on it. *)
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import FinInput.
From OSSVerify.Tests.proofs.lib Require Import EbreakInstance.
From OSSVerify.Tests.toy.ebreak Require Images.
Import ListNotations.

Lemma asan_agreement_decidable_alloc_forced_only_instance :
  valid_fin_input (fin_input refused_by_driver [])
  /\ (exists ep es, valid_entry Images.plain ep (to_proc_input (fin_input refused_by_driver []))
                    /\ valid_entry Images.asan es (to_proc_input (fin_input refused_by_driver []))).
Proof. exact (fin_premises _ _ launch_argv_refused_by_driver). Qed.
