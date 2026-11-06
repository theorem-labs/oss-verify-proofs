(** * toy / ebreak: the images

    Two toy images of linux-process-semantics's own tests, used as they
    are there, in the roles a harness's builds play (named as the generator
    names a plain and an ASan build, so that Statements.v is word for word
    what the generator writes):
      plain  [Checks.Omni.ebreak_image]: one ebreak at its entry point, an
             instruction lps models as a fault, so its one execution
             reaches an error at once, before any system call;
      asan   [Checks.Examples.exit0_image]: three instructions that call
             exit_group(0).  It is not a sanitizer build.
    lps refutes its agreement statements with this pair
    ([Checks.BudgetPremise.ebreak_refutes_error_free_budgets] and its
    siblings); tests/proofs/toy/ebreak/ fires those refutations, and builds
    the ones lps does not have, at the exact budgets, environments and exit
    sets this collection's statements use (Statements.v). *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples Omni.

Definition plain : Image := ebreak_image.
Definition asan : Image := exit0_image.
