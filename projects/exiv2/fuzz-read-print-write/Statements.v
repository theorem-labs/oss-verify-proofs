(** * exiv2 / fuzz-read-print-write: theorem statements

    SUBJECT.  Four builds of exiv2's own fuzz target [fuzz-read-print-write], as
    OSS-Fuzz builds it, for exiv2 (Exiv2/exiv2 at e84cb9db), static riscv64
    Linux programs run as [<file> FILE]:
      plain       no sanitizer
      ubsan       UndefinedBehaviorSanitizer; a failed check executes a trap
      asan        AddressSanitizer; a report aborts
      asan_ubsan  both
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

    WHAT THE HARNESS CHECKS.  readMetadata; print every Exif/IPTC/XMP datum;
    printStructure in six modes into a string stream; writeMetadata back into
    the in-memory image; nothing compared.  The harness checks:
    (a) ImageFactory::open must never return a null image (it throws on unknown
    formats instead) [assert(); confirmed in the binary]
    Each check was confirmed in the binary: its assertion text or message is in
    the binary's bytes.

    Whether each statement is open, proved or known false is recorded in the
    harness README, not here: this file changes only when a statement does. *)

From Stdlib Require Import QArith.
From OssFuzzTheorems.Core Require Import Shapes.
From OssFuzzTheorems.exiv2.fuzz_read_print_write Require Images.

(** ** Halting *)

(** On every input on which the plain build is never refused memory for
    exceeding 16 GiB, and when the environment refuses nothing it is not forced
    to, every execution of the plain build exits with status 0 or 2.  It never
    crashes, fails an assertion, hangs, or leaves the model.  Check (a) ends the
    process when it fails, which this statement excludes, so a proof establishes
    it for the code in this binary on every input it covers.

    Not claimed: anything about what the program writes; anything about other
    compilers, architectures or exiv2 commits. *)
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
    instruments (the harness, exiv2 and the driver, less the code the harness
    README lists as uninstrumented).  Stated with abort() read as death by
    SIGABRT rather than as a step the model does not cover; the statement still
    forbids it.

    Not claimed: anything about inputs on which the plain build needs more than
    2 GiB; memory errors ASan does not detect (for example an access that lands
    inside another live object, or one made in code it does not instrument). *)
Definition asan_agrees : Prop :=
  agrees_in_abort_modelled Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan.

(** As [asan_agrees], for the UBSan build, with 16 GiB for the plain build.  A
    failed UBSan check traps, so a proof shows that no UBSan check in this build
    fails on any such input.  Stated with abort() read as death by SIGABRT
    rather than as a step the model does not cover; the statement still forbids
    it. *)
Definition ubsan_agrees : Prop :=
  agrees_in_abort_modelled Env.alloc_forced_only Budgets.Standard.lim_source Budgets.Standard.lim_target Images.plain Images.ubsan.

(** As [asan_agrees], for the ASan+UBSan build, with 2 GiB for the plain build.
    An ASan report aborts and a failed UBSan check traps, so a proof shows that
    neither sanitizer fires on any such input in the code they instrument (the
    harness, exiv2 and the driver, less the code the harness README lists as
    uninstrumented).  Stated with abort() read as death by SIGABRT rather than
    as a step the model does not cover; the statement still forbids it. *)
Definition asan_ubsan_agrees : Prop :=
  agrees_in_abort_modelled Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan_ubsan.

(** ** Proving a statement

    A proof is a directory proofs/exiv2/fuzz-read-print-write/<statement>/ whose
    Proof.v ends, for example, in
      Theorem plain_halts_holds : Statements.plain_halts.

    See docs/proving.md. *)
