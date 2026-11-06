(** * liboqs / fuzz_test_sig: theorem statements

    SUBJECT.  Four builds of liboqs's own fuzz target [fuzz_test_sig], as
    OSS-Fuzz builds it, for liboqs (open-quantum-safe/liboqs at 8979276a),
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

    WHAT THE HARNESS CHECKS.  Checks one property, a self-validation: A
    signature just produced by OQS_SIG_sign over the fuzz message (fuzz-selected
    algorithm, fuzz-seeded RNG keypair) must verify with OQS_SIG_verify under
    the matching public key.  The harness checks:
    (a) A signature just produced by OQS_SIG_sign over the fuzz message
    (fuzz-selected algorithm, fuzz-seeded RNG keypair) must verify with
    OQS_SIG_verify under the matching public key. [exit(1); not confirmed in the
    binary]
    Only the checks marked ''confirmed in the binary'' had their assertion text
    or message found in the binary's bytes; for the others no usable text was
    found, which does not mean that they are compiled out, and no statement
    below relies on them.

    Whether each statement is open, proved or known false is recorded in the
    harness README, not here: this file changes only when a statement does. *)

From Stdlib Require Import QArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.liboqs.fuzz_test_sig Require Images.

(** ** Halting *)

(** On every input on which the plain build is never refused memory for
    exceeding 16 GiB, and when the environment refuses nothing it is not forced
    to, every execution of the plain build exits with status 0 or 2.  It never
    crashes, fails an assertion, hangs, or leaves the model.

    Not claimed: anything about what the program writes; anything about other
    compilers, architectures or liboqs commits. *)
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

(** Every execution of the plain build exits, with any status, on every input
    and whatever the environment refuses (any allocation, open or read may fail
    at any time).  It covers every input and any refusal, unlike [plain_halts],
    but allows any exit status.  There is no ASan statement of this form: the
    ASan runtime deliberately waits forever when its start-up reservation is
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
    exceeding 2 GiB, whatever the environment refuses in either build: neither
    build ever faults, aborts or leaves the model, and the two write the same
    bytes and exit with the same status.  An ASan report aborts, so a proof
    shows that ASan reports nothing on any such input: no memory error that this
    build's ASan detects happens in the code it instruments (the harness, liboqs
    and the driver, less the code the harness README lists as uninstrumented).

    Not claimed: anything about inputs on which the plain build needs more than
    2 GiB; memory errors ASan does not detect (for example an access that lands
    inside another live object, or one made in code it does not instrument). *)
Definition asan_agrees : Prop :=
  agrees Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan.

(** As [asan_agrees], for the UBSan build, with 16 GiB for the plain build.  A
    failed UBSan check traps, so a proof shows that no UBSan check in this build
    fails on any such input. *)
Definition ubsan_agrees : Prop :=
  agrees Budgets.Standard.lim_source Budgets.Standard.lim_target Images.plain Images.ubsan.

(** As [asan_agrees], for the ASan+UBSan build, with 2 GiB for the plain build.
    An ASan report aborts and a failed UBSan check traps, so a proof shows that
    neither sanitizer fires on any such input in the code they instrument (the
    harness, liboqs and the driver, less the code the harness README lists as
    uninstrumented). *)
Definition asan_ubsan_agrees : Prop :=
  agrees Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan_ubsan.

(** ** Proving a statement

    A proof is a directory named after the statement, in this fuzz target's
    proofs folder (docs/proving.md says where it is), whose Proof.v ends, for
    example, in
      Theorem plain_halts_holds : Statements.plain_halts.

    See docs/proving.md. *)
