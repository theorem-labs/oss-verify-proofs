(** POSITIVE CONTROL: the instance of
    toy/ebreak/asan_disagrees_at_most_may_fail, of the shape
    [disagrees_at_most].  Its file, input.bin, holds the 7 bytes
    [EbreakInstance.seven], and its path is reaches-harness: argv is
    ["ebreak"; "input.bin"].  The instance is a finite input, the one a
    Distribution.v builds over the file system [("input.bin", [])] with
    those bytes in the file.  It is valid, and both builds have a valid
    entry on it. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import FinInput.
From OSSVerify.Tests.proofs.lib Require Import EbreakInstance.
From OSSVerify.Tests.toy.ebreak Require Images.

Lemma asan_disagrees_at_most_may_fail_instance :
  valid_fin_input (fin_input reaches_harness seven)
  /\ (exists ep es, valid_entry Images.plain ep (to_proc_input (fin_input reaches_harness seven))
                    /\ valid_entry Images.asan es (to_proc_input (fin_input reaches_harness seven))).
Proof. exact (fin_premises _ _ launch_argv_reaches_harness). Qed.
