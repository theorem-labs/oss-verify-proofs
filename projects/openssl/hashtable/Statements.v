(** * openssl / hashtable: theorem statements

    SUBJECT.  Four builds of openssl's own fuzz target [hashtable], as OSS-Fuzz
    builds it, for openssl (openssl/openssl at 47aae188), static riscv64 Linux
    programs run as [<file> FILE]:
      plain       no sanitizer
      ubsan       UndefinedBehaviorSanitizer; a failed check executes a trap
      asan        AddressSanitizer; a report aborts
      asan_ubsan  both
    [Images] names their memory images.  A driver linked into every build reads
    FILE as [u16 config word][config bytes][u32 allocation mask][payload]
    (little-endian; the low 15 bits of the config word are the config length,
    and this harness binary ignores the mask), calls FuzzerTestOneInput(payload,
    length) one to four times ((config[0] & 3) + 1; once when there is no
    config), and prints each return value.  With a wrong argument count, a
    missing or unreadable FILE, a FILE shorter than its header, or one of 64 MiB
    or more, it exits with status 2 without calling the harness.  Every
    statement quantifies over all of these cases and over every other process
    input (see Vocabulary in OssFuzzTheorems.Core.Shapes).

    WHAT THE HARNESS CHECKS.  Checks 3 properties (listed below); the first, a
    reference oracle: OP_FOREACH: ossl_ht_foreach_until finds the key's value
    iff the prediction table marks it allocated; OP_FILTER: ossl_ht_filter
    returns exactly 0 or 1 matching value as predicted. Only an empty table in a
    single-input run.  The harness checks:
    (a) OP_FOREACH: ossl_ht_foreach_until finds the key's value iff the
    prediction table marks it allocated; OP_FILTER: ossl_ht_filter returns
    exactly 0 or 1 matching value as predicted. Only an empty table in a
    single-input run. [abort(); confirmed in the binary]
    Each check was confirmed in the binary: its assertion text or message is in
    the binary's bytes.

    Whether each statement is open, proved or known false is recorded in the
    harness README, not here: this file changes only when a statement does. *)

From Stdlib Require Import QArith.
From OssFuzzTheorems.Core Require Import Shapes.
From OssFuzzTheorems.openssl.hashtable Require Images Distribution.

(** ** Halting *)

(** On every input on which the plain build is never refused memory for
    exceeding 16 GiB, and when the environment refuses nothing it is not forced
    to, every execution of the plain build exits with status 0 or 2.  It never
    crashes, fails an assertion, hangs, or leaves the model.  Check (a) ends the
    process when it fails, which this statement excludes, so a proof establishes
    it for the code in this binary on every input it covers.

    Not claimed: anything about what the program writes; anything about other
    compilers, architectures or openssl commits. *)
Definition plain_halts : Prop :=
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused Images.plain.

(** As [plain_halts], for the UBSan build.  A failed UBSan check traps, so a
    proof also shows that no check UBSan makes in this build fails on any such
    input. *)
Definition ubsan_halts : Prop :=
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused Images.ubsan.

(** As [plain_halts], for the ASan build.  An ASan report aborts, so a proof
    also shows that ASan detects no memory error, in the code it instruments, on
    any such input (the harness README lists the code this build links
    uninstrumented).  The runtime's own address-space reservations are not
    charged to the budget. *)
Definition asan_halts : Prop :=
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused Images.asan.

(** As [plain_halts], for the ASan+UBSan build.  An ASan report aborts and a
    failed UBSan check traps, so a proof also shows that neither sanitizer
    fires, in the code they instrument, on any such input (the harness README
    lists the code this build links uninstrumented). *)
Definition asan_ubsan_halts : Prop :=
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused Images.asan_ubsan.

(** ** Agreement of each sanitizer build with the plain build *)

(** On every input on which the plain build is never refused memory for
    exceeding 2 GiB, when a memory request is refused only if the budget is
    spent or no address range is free (any other request may still be refused,
    in either build): neither build ever faults, aborts or leaves the model, and
    the two write the same bytes and exit with the same status.  An ASan report
    aborts, so a proof shows that ASan reports nothing on any such input: no
    memory error that this build's ASan detects happens in the code it
    instruments (the harness, openssl and the driver, less the code the harness
    README lists as uninstrumented).

    Not claimed: anything about inputs on which the plain build needs more than
    2 GiB; memory errors ASan does not detect (for example an access that lands
    inside another live object, or one made in code it does not instrument). *)
Definition asan_agrees : Prop :=
  agrees_in Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan.

(** As [asan_agrees], for the UBSan build, with 16 GiB for the plain build.  A
    failed UBSan check traps, so a proof shows that no UBSan check in this build
    fails on any such input. *)
Definition ubsan_agrees : Prop :=
  agrees_in Env.alloc_forced_only Budgets.Standard.lim_source Budgets.Standard.lim_target Images.plain Images.ubsan.

(** As [asan_agrees], for the ASan+UBSan build, with 2 GiB for the plain build.
    An ASan report aborts and a failed UBSan check traps, so a proof shows that
    neither sanitizer fires on any such input in the code they instrument (the
    harness, openssl and the driver, less the code the harness README lists as
    uninstrumented). *)
Definition asan_ubsan_agrees : Prop :=
  agrees_in Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan_ubsan.

(** ** How often the builds disagree *)

(** For an input drawn from [Distribution.w] (Distribution.v), the probability
    that the plain and ASan builds are not both error-free with equal traces is
    at most [b].  Agreement here is judged at 16 GiB / 512 GiB with no budget
    premise (Core.Shapes), so [asan_agrees] does not by itself give
    [asan_disagrees_at_most 0].  Smaller [b] is stronger; [b = 1] holds
    trivially. *)
Definition asan_disagrees_at_most (b : Q) : Prop :=
  disagrees_at_most Env.alloc_forced_only Distribution.w Distribution.M Images.plain Images.asan b.

(** As [asan_disagrees_at_most], for the UBSan build. *)
Definition ubsan_disagrees_at_most (b : Q) : Prop :=
  disagrees_at_most Env.alloc_forced_only Distribution.w Distribution.M Images.plain Images.ubsan b.

(** As [asan_disagrees_at_most], for the ASan+UBSan build. *)
Definition asan_ubsan_disagrees_at_most (b : Q) : Prop :=
  disagrees_at_most Env.alloc_forced_only Distribution.w Distribution.M Images.plain Images.asan_ubsan b.

(** ** Deciding where the builds agree *)

(** Some well-formed riscv64 program decides exactly the finite inputs on which
    the plain and ASan builds agree ([Characterise.v] states the problem for a
    given program). *)
Definition asan_agreement_decidable : Prop :=
  agreement_decidable Env.alloc_forced_only Images.plain Images.asan.

(** As [asan_agreement_decidable], for the UBSan build. *)
Definition ubsan_agreement_decidable : Prop :=
  agreement_decidable Env.alloc_forced_only Images.plain Images.ubsan.

(** As [asan_agreement_decidable], for the ASan+UBSan build. *)
Definition asan_ubsan_agreement_decidable : Prop :=
  agreement_decidable Env.alloc_forced_only Images.plain Images.asan_ubsan.

(** ** Proving a statement

    A proof is a directory proofs/openssl/hashtable/<statement>/ whose Proof.v
    ends, for example, in
      Theorem plain_halts_holds : Statements.plain_halts.
    A bound proof names its bound:
      Theorem asan_disagrees_at_most_holds : Statements.asan_disagrees_at_most (1 # 1000).
    See docs/proving.md. *)
