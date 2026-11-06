(** * libreac / fuzz_identity: theorem statements

    SUBJECT.  Four builds of libreac's own fuzz target [fuzz_identity], which
    OSS-Fuzz does not run, for libreac 1.9.0 (FreeREAC/libreac at d16f3f4e),
    static riscv64 Linux programs run as [<file> FILE]:
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
    other process input (see Vocabulary in OSSVerify.Core.Shapes).

    WHAT THE HARNESS CHECKS.  Reads the payload as up to 64 identity-page
    records (a 16-bit address, biased onto the three modelled ones, and a
    payload in its own allocation) fed to reac_identity_ingest, each a second
    time with a guard byte after it, then as the box family, channel widths,
    capacities and a firmware value with which it calls the firmware and
    REAC-version formatters, reac_box_name and the catalogue defect check, each
    output buffer its own allocation of the chosen size.  The harness checks:
    (a) The decode reads no byte past the length it is given (a guard byte after
    the payload changes nothing), an ignored record changes nothing, and a
    well-formed firmware, REAC-version or model-name record is never ignored.
    [abort(); not confirmed in the binary]
    (b) An accepted firmware reply is four decimal digits printed as D.DDD, a
    model name is the payload's text after its first byte, up to its first NUL
    or the name field's capacity, and never empty, and a REAC-version record
    keeps its eight bytes, decodes the last three words big-endian and prints as
    major.minor with a patch of two digits or more; no other address is
    accepted. [abort(); not confirmed in the binary]
    (c) Each formatter either refuses or writes a NUL-terminated string of the
    length it returns inside the capacity it was given. [abort(); not confirmed
    in the binary]
    (d) The firmware formatter prints any value as its whole part, '.', and
    three digits, also when the whole part has two digits. [abort(); not
    confirmed in the binary]
    (e) The box family is the one the last accepted REAC-version record names in
    the documented table, and UNKNOWN with no such record or one no row names.
    [abort(); not confirmed in the binary]
    (f) reac_box_name refuses a NULL name buffer or a bad width, and with good
    widths succeeds exactly when each buffer holds its string; the name is the
    sent name or family stem plus the two-digit widths, the token is the name
    lower-cased with its first '-' dropped, the display is ''<name> (<in> in /
    <out> out)'', and the catalogue defect mask flags exactly a width or display
    mismatch. [abort(); not confirmed in the binary]
    (g) The documented refusals of NULL arguments hold. [abort(); not confirmed
    in the binary]
    Only the checks marked ''confirmed in the binary'' had their assertion text
    or message found in the binary's bytes; for the others no usable text was
    found, which does not mean that they are compiled out, and no statement
    below relies on them.

    Whether each statement is open, proved or known false is recorded in the
    harness README, not here: this file changes only when a statement does. *)

From Stdlib Require Import QArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_identity Require Images.

(** ** Halting *)

(** On every input on which the plain build is never refused memory for
    exceeding 16 GiB, and when the environment refuses nothing it is not forced
    to, every execution of the plain build exits with status 0 or 2.  It never
    crashes, fails an assertion, hangs, or leaves the model.

    Not claimed: anything about what the program writes; anything about other
    compilers, architectures or libreac commits. *)
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
    instruments (the harness, libreac and the driver, less the code the harness
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
    harness, libreac and the driver, less the code the harness README lists as
    uninstrumented). *)
Definition asan_ubsan_agrees : Prop :=
  agrees_in Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan_ubsan.

(** ** Proving a statement

    A proof is a directory named after the statement, in this fuzz target's
    proofs folder (docs/proving.md says where it is), whose Proof.v ends, for
    example, in
      Theorem plain_halts_holds : Statements.plain_halts.

    See docs/proving.md. *)
