(** * omx-dsp / fuzz_delay: theorem statements

    SUBJECT.  Four builds of omx-dsp's own fuzz target [fuzz_delay], which
    OSS-Fuzz does not run, for omx-dsp 0.27.0 (FreeMixer/omx-dsp at a0ee1dfe),
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

    WHAT THE HARNESS CHECKS.  Reads a flags byte and a ring size of 1 to 4096.
    The fractional mode arms a Lagrange delay line of order 3, order 5 or any
    signed byte, and runs up to 12 finite blocks, each with any float delay. The
    integer mode runs up to 12 blocks of a stereo or mono integer delay pair,
    with delays in tenths of a millisecond at a declared rate. It can also check
    the ms-to-samples conversion for any finite ms and rate. The harness keeps
    its own copy of the take as the oracle.  The harness checks:
    (a) A ring takes a line exactly when the order is 3 or 5 and the ring is
    longer than the kernel's reach. A refusal returns the code that names its
    cause and leaves the line unarmed. [abort(); not confirmed in the binary]
    (b) An unarmed line reports a latency of 0 and leaves the block unchanged,
    bit for bit. [abort(); not confirmed in the binary]
    (c) The delay delivered is finite and inside the ring's longest delay, and a
    non-finite request reads as 0. The delay also equals the harness's own
    reading of the rule in the library's comment. [abort(); not confirmed in the
    binary]
    (d) Every sample from the fractional line is finite and no larger than the
    absolute sum of the Lagrange weights times the take's peak. [abort(); not
    confirmed in the binary]
    (e) A whole-sample delay outputs the take delayed by that many samples, bit
    for bit, with zero before the take starts. [abort(); not confirmed in the
    binary]
    (f) A fractional delay outputs the Lagrange sum, computed by the harness
    over its copy of the take, to within a tolerance scaled by the weights and
    the peak. [abort(); not confirmed in the binary]
    (g) omx_idelay_samples is inside the ring. It is the rounded delay saturated
    at the ring's last slot, and 0 for a delay of no length. This holds both for
    any finite ms and rate and for the grid's ms and declared rates. [abort();
    not confirmed in the binary]
    (h) A steady integer delay on either leg outputs the take delayed, bit for
    bit. [abort(); not confirmed in the binary]
    (i) While the integer delay moves, each sample on either leg stays between
    the old tap and the new tap it fades across. [abort(); not confirmed in the
    binary]
    (j) At the end of the input, no contract of the library is recorded as
    broken. The ledger is emptied after the calls whose PRE the harness breaks
    on purpose. [abort(); not confirmed in the binary]
    Only the checks marked ''confirmed in the binary'' had their assertion text
    or message found in the binary's bytes; for the others no usable text was
    found, which does not mean that they are compiled out, and no statement
    below relies on them.

    Whether each statement is open, proved or known false is recorded in the
    harness README, not here: this file changes only when a statement does. *)

From Stdlib Require Import QArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_dsp.fuzz_delay Require Images.

(** ** Halting *)

(** On every input on which the plain build is never refused memory for
    exceeding 16 GiB, and when the environment refuses nothing it is not forced
    to, every execution of the plain build exits with status 0 or 2.  It never
    crashes, fails an assertion, hangs, or leaves the model.

    Not claimed: anything about what the program writes; anything about other
    compilers, architectures or omx-dsp commits. *)
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
    instruments (the harness, omx-dsp and the driver, less the code the harness
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
    harness, omx-dsp and the driver, less the code the harness README lists as
    uninstrumented). *)
Definition asan_ubsan_agrees : Prop :=
  agrees_in Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan_ubsan.

(** ** Proving a statement

    A proof is a directory named after the statement, in this fuzz target's
    proofs folder (docs/proving.md says where it is), whose Proof.v ends, for
    example, in
      Theorem plain_halts_holds : Statements.plain_halts.

    See docs/proving.md. *)
