(** * avahi / fuzz-packet: theorem statements

    SUBJECT.  Two builds of avahi's own fuzz target [fuzz-packet], as OSS-Fuzz
    builds it, for avahi (avahi/avahi at b1a83592), static riscv64 Linux
    programs run as [<file> FILE]:
      plain       no sanitizer
      ubsan       UndefinedBehaviorSanitizer; a failed check executes a trap
    [Images] names their memory images.  A driver linked into every build reads
    FILE as [u16 config word][config bytes][u32 allocation mask][payload]
    (little-endian; the low 15 bits of the config word are the config length,
    and this harness binary ignores the mask), calls
    LLVMFuzzerTestOneInput(payload, length) one to four times ((config[0] & 3) +
    1; once when there is no config), and prints each return value.  With a
    wrong argument count, a missing or unreadable FILE, a FILE shorter than its
    header, or one of 64 MiB or more, it exits with status 2 without calling the
    harness.  Every statement quantifies over all of these cases and over every
    other process input (see Vocabulary in OssFuzzTheorems.Core.Shapes).

    WHAT THE HARNESS CHECKS.  Checks 2 properties (listed below); the first, an
    API contract: same split -> join success contract without the service-name
    part.  The harness checks:
    (a) same split -> join success contract without the service-name part
    [assert(); confirmed in the binary]
    Each check was confirmed in the binary: its assertion text or message is in
    the binary's bytes.

    Whether each statement is open, proved or known false is recorded in the
    harness README, not here: this file changes only when a statement does. *)

From Stdlib Require Import QArith.
From OssFuzzTheorems.Core Require Import Shapes.
From OssFuzzTheorems.avahi.fuzz_packet Require Images Distribution.

(** ** Halting *)

(** On every input on which the plain build is never refused memory for
    exceeding 16 GiB, and when the environment refuses nothing it is not forced
    to, every execution of the plain build exits with status 0 or 2.  It never
    crashes, fails an assertion, hangs, or leaves the model.  Check (a) ends the
    process when it fails, which this statement excludes, so a proof establishes
    it for the code in this binary on every input it covers.

    Not claimed: anything about what the program writes; anything about other
    compilers, architectures or avahi commits. *)
Definition plain_halts : Prop :=
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused Images.plain.

(** As [plain_halts], for the UBSan build.  A failed UBSan check traps, so a
    proof also shows that no check UBSan makes in this build fails on any such
    input. *)
Definition ubsan_halts : Prop :=
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused Images.ubsan.

(** Every execution of the plain build exits, with any status, on every input
    and whatever the environment refuses (any allocation, open or read may fail
    at any time).  It covers every input and any refusal, unlike [plain_halts],
    but allows any exit status.  Check (a) ends the process when it fails, which
    this statement excludes, so a proof establishes it for the code in this
    binary on every input it covers.  There is no ASan statement of this form:
    the ASan runtime deliberately waits forever when its start-up reservation is
    refused, so such a statement would be false for a reason that has nothing to
    do with this harness.

    Not claimed: anything about what the program writes. *)
Definition plain_halts_may_fail : Prop :=
  halts_may_fail Exits.any Images.plain.

(** As [plain_halts_may_fail], for the UBSan build.  It covers every input and
    any refusal, unlike [ubsan_halts], but allows any exit status.  A failed
    UBSan check traps, so a proof also shows that no check UBSan makes in this
    build fails on any such input. *)
Definition ubsan_halts_may_fail : Prop :=
  halts_may_fail Exits.any Images.ubsan.

(** ** Agreement of each sanitizer build with the plain build *)

(** On every input on which the plain build is never refused memory for
    exceeding 16 GiB, whatever the environment refuses in either build: neither
    build ever faults, aborts or leaves the model, and the two write the same
    bytes and exit with the same status.  A failed UBSan check traps, so a proof
    shows that no UBSan check in this build fails on any such input.

    Not claimed: anything about inputs on which the plain build needs more than
    16 GiB. *)
Definition ubsan_agrees : Prop :=
  agrees Budgets.Standard.lim_source Budgets.Standard.lim_target Images.plain Images.ubsan.

(** ** How often the builds disagree *)

(** For an input drawn from [Distribution.w] (Distribution.v), the probability
    that the plain and UBSan builds are not both error-free with equal traces is
    at most [b].  Agreement here is judged at 16 GiB / 512 GiB with no budget
    premise (Core.Shapes), so [ubsan_agrees] does not by itself give
    [ubsan_disagrees_at_most 0].  Smaller [b] is stronger; [b = 1] holds
    trivially. *)
Definition ubsan_disagrees_at_most (b : Q) : Prop :=
  disagrees_at_most Env.may_fail Distribution.w Distribution.M Images.plain Images.ubsan b.

(** ** Deciding where the builds agree *)

(** Some well-formed riscv64 program decides exactly the finite inputs on which
    the plain and UBSan builds agree ([Characterise.v] states the problem for a
    given program). *)
Definition ubsan_agreement_decidable : Prop :=
  agreement_decidable Env.may_fail Images.plain Images.ubsan.

(** ** Proving a statement

    A proof is a directory proofs/avahi/fuzz-packet/<statement>/ whose Proof.v
    ends, for example, in
      Theorem plain_halts_holds : Statements.plain_halts.
    A bound proof names its bound:
      Theorem ubsan_disagrees_at_most_holds : Statements.ubsan_disagrees_at_most (1 # 1000).
    See docs/proving.md. *)
