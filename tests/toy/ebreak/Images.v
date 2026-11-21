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
    sets this collection's statements use (Statements.v).

    The classifier statements name more images, in the roles the generator
    names for the pair's two classifiers and its originals, again lps's own:
      classifier_a_asan, classifier_b_asan
             [Checks.Omni.ebreak_image]: a classifier that gives no answer,
             since its one run faults before it can exit;
      plain_original, asan_original
             the builds' own images, as for a harness without patches.
    The soundness statements take their classifier as a parameter (a
    classifier that gives no answer is sound for every property), and are
    controlled through two more:
      always_yes  [Checks.Examples.exit0_image], which exits 0, "yes", from
             every entry on every input;
      always_no   [Checks.GatedSize.exit1_image], the same three instructions
             with exit_group(1), "no". *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples Omni GatedSize.

Definition plain : Image := ebreak_image.
Definition asan : Image := exit0_image.

Definition classifier_a_asan : Image := ebreak_image.
Definition classifier_b_asan : Image := ebreak_image.
Definition plain_original : Image := ebreak_image.
Definition asan_original : Image := exit0_image.

Definition always_yes : Image := exit0_image.
Definition always_no : Image := exit1_image.
