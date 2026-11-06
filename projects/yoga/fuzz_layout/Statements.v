(** * yoga / fuzz_layout: theorem statements

    SUBJECT.  Two builds of yoga's own fuzz target [fuzz_layout], as OSS-Fuzz
    builds it, for yoga (facebook/yoga at 433d4634), static riscv64 Linux
    programs run as [<file> FILE]:
      plain       no sanitizer
      asan        AddressSanitizer; a report aborts
    [Images] names their memory images.  A driver linked into every build reads
    FILE as [u16 config word][config bytes][u32 allocation mask][payload]
    (little-endian; the low 15 bits of the config word are the config length,
    and this harness binary ignores the mask), calls
    LLVMFuzzerTestOneInput(payload, length) one to four times ((config[0] & 3) +
    1; once when there is no config), and prints each return value.  With a
    wrong argument count, a missing or unreadable FILE, a FILE shorter than its
    header, or one of 64 MiB or more, it exits with status 2 without calling the
    harness.  Every statement quantifies over all of these cases and over every
    other process input (see Vocabulary in OSSVerify.Core.Shapes).

    WHAT THE HARNESS CHECKS.  Builds a random node tree (depth <= 20, <= 20
    children per node, random flex direction, width, height, gap), runs
    YGNodeCalculateLayout once and frees it; the computed layout is never read
    or checked.  The harness makes no check of its own beyond not crashing, so a
    statement about it says only that the code it calls never crashes, hangs or
    trips a sanitizer.

    Whether each statement is open, proved or known false is recorded in the
    harness README, not here: this file changes only when a statement does. *)

From Stdlib Require Import QArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.yoga.fuzz_layout Require Images Distribution.

(** ** Halting *)

(** On every input on which the plain build is never refused memory for
    exceeding 16 GiB, and when the environment refuses nothing it is not forced
    to, every execution of the plain build exits with status 0 or 2.  It never
    crashes, fails an assertion, hangs, or leaves the model.

    Not claimed: anything about what the program writes; anything about other
    compilers, architectures or yoga commits. *)
Definition plain_halts : Prop :=
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused Images.plain.

(** As [plain_halts], for the ASan build.  An ASan report aborts, so a proof
    also shows that ASan detects no memory error, in the code it instruments, on
    any such input (the harness README lists the code this build links
    uninstrumented).  The runtime's own address-space reservations are not
    charged to the budget. *)
Definition asan_halts : Prop :=
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused Images.asan.

(** ** Agreement of each sanitizer build with the plain build *)

(** On every input on which the plain build is never refused memory for
    exceeding 2 GiB, when a memory request is refused only if the budget is
    spent or no address range is free (any other request may still be refused,
    in either build): neither build ever faults, aborts or leaves the model, and
    the two write the same bytes and exit with the same status.  An ASan report
    aborts, so a proof shows that ASan reports nothing on any such input: no
    memory error that this build's ASan detects happens in the code it
    instruments (the harness, yoga and the driver, less the code the harness
    README lists as uninstrumented).  Stated with abort() read as death by
    SIGABRT rather than as a step the model does not cover; the statement still
    forbids it.

    Not claimed: anything about inputs on which the plain build needs more than
    2 GiB; memory errors ASan does not detect (for example an access that lands
    inside another live object, or one made in code it does not instrument). *)
Definition asan_agrees : Prop :=
  agrees_in_abort_modelled Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan.

(** ** How often the builds disagree *)

(** For an input drawn from [Distribution.w] (Distribution.v), the probability
    that the plain and ASan builds are not both error-free with equal traces is
    at most [b].  Agreement here is judged at 16 GiB / 512 GiB with no budget
    premise (Core.Shapes), so [asan_agrees] does not by itself give
    [asan_disagrees_at_most 0].  Smaller [b] is stronger; [b = 1] holds
    trivially. *)
Definition asan_disagrees_at_most (b : Q) : Prop :=
  disagrees_at_most Env.alloc_forced_only Distribution.w Distribution.M Images.plain Images.asan b.

(** ** Deciding where the builds agree *)

(** Some well-formed riscv64 program decides exactly the finite inputs on which
    the plain and ASan builds agree ([Characterise.v] states the problem for a
    given program). *)
Definition asan_agreement_decidable : Prop :=
  agreement_decidable Env.alloc_forced_only Images.plain Images.asan.

(** ** Proving a statement

    A proof is a directory named after the statement, in this fuzz target's
    proofs folder (docs/proving.md says where it is), whose Proof.v ends, for
    example, in
      Theorem plain_halts_holds : Statements.plain_halts.
    A bound proof names its bound:
      Theorem asan_disagrees_at_most_holds : Statements.asan_disagrees_at_most (1 # 1000).
    See docs/proving.md. *)
