(** POSITIVE CONTROL: the instance of
    toy/ebreak/asan_agreement_decidable_rv64gc_may_fail, of the shape
    [agreement_decidable_rv64gc].  Its file, input.bin, holds the 7 bytes
    [EbreakInstance.seven], and its path is reaches-harness: argv is
    ["ebreak"; "input.bin"].  The instance is a finite input, the one a
    Distribution.v builds over the file system [("input.bin", [])] with
    those bytes in the file.  It is valid, its AT_HWCAP word is RV64GC's,
    and both builds have a valid entry on it. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import FinInput.
From OSSVerify.Tests.proofs.lib Require Import EbreakInstance.
From OSSVerify.Tests.toy.ebreak Require Images.

Lemma asan_agreement_decidable_rv64gc_may_fail_instance :
  valid_fin_input (fin_input reaches_harness seven)
  /\ in_hwcap (to_proc_input (fin_input reaches_harness seven)) = hwcap_rv64gc
  /\ (exists ep es, valid_entry Images.plain ep (to_proc_input (fin_input reaches_harness seven))
                    /\ valid_entry Images.asan es (to_proc_input (fin_input reaches_harness seven))).
Proof. exact (fin_premises_rv64gc _ _ launch_argv_reaches_harness). Qed.
