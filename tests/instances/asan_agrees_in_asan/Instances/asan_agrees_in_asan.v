(** POSITIVE CONTROL: the instance of toy/ebreak/asan_agrees_in_asan, of
    the shape [agrees_in].  Its file, input.bin, holds the 7 bytes
    [EbreakInstance.seven], and its path is reaches-harness: argv is
    ["ebreak"; "input.bin"].  On that input the premises of [agrees_in] at
    the ASan budgets hold together: valid entries of both builds, a valid
    input, and a run of the plain build under [Env.alloc_forced_only] that
    is never refused memory. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.proofs.lib Require Import EbreakInstance.
From OSSVerify.Tests.toy.ebreak Require Images.

Lemma asan_agrees_in_asan_instance :
  exists ep es, valid_entry Images.plain ep (input false reaches_harness seven)
    /\ valid_entry Images.asan es (input false reaches_harness seven)
    /\ valid_input (input false reaches_harness seven)
    /\ ~ run_scfg_budget_refused Env.alloc_forced_only Images.plain Budgets.Asan.lim_source ep
           (input false reaches_harness seven).
Proof. exact (agrees_in_premises _ _ _ _ launch_argv_reaches_harness). Qed.
