(** * libdiginet / fuzz_transport: theorem statements

    SUBJECT.  Four builds of libdiginet's own fuzz target [fuzz_transport],
    which OSS-Fuzz does not run, for libdiginet 0.1.1 (FreeMixer/libdiginet at
    835f336c), static riscv64 Linux programs run as [<file> FILE]:
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

    WHAT THE HARNESS CHECKS.  Runs the library's control-surface session state
    machine with the harness as its network io and clock. A config is read from
    the input, then up to 1024 operations: raw or built desk frames, announces,
    time passing, submitted commands, wake, close, a failing send, and polls.
    The harness runs its own model of the documented session alongside and holds
    every frame sent, every notice, the state, the timers and the command queue
    to that model. Inputs of 64 MiB or more are ignored.  The harness checks:
    (a) The session accepts every configuration the harness builds, each within
    the documented ranges. [abort(); not confirmed in the binary]
    (b) Every frame the session sends is a well-formed frame from this host to
    the known desk, zero-padded to 60 bytes, with the right header sum, and
    never holds the system family F0 13 xx 70. [abort(); not confirmed in the
    binary]
    (c) Each acknowledgement the session sends echoes the send counter of the
    desk frame it answers, with no body and retry 0. [abort(); not confirmed in
    the binary]
    (d) A new data frame goes only while online, with nothing in flight and no
    back-off holding; a retransmission is the frame in flight again, byte for
    byte but its retry field, which counts 1, 2, ... never past the retry limit,
    and goes no sooner than the timeout; the acked notice names the frame in
    flight; the ack-lost notice comes for it after exactly the retry limit.
    [abort(); not confirmed in the binary]
    (e) Online only after the desk acknowledges the wake frame and an e1 names
    this host since then; no wake frame while the desk is in a session with
    another host, and a wake returns the documented code; each desk announce
    notice carries the place of this host address, the desk type, the version
    and the name, and each desk data notice its body, counter and retry.
    [abort(); not confirmed in the binary]
    (f) A keepalive goes only when due on its own clock, while online, with
    nothing in flight and no back-off holding: never early. [abort(); not
    confirmed in the binary]
    (g) Each sent data frame stays within the command and body limits and
    carries the host counter advanced by its commands; with tagged commands, its
    count is right, it carries only commands submitted and still pending, and a
    frame with display writes follows the last by at least the configured gap.
    [abort(); not confirmed in the binary]
    (h) Submit refuses a command holding F0 13 xx 70 and nothing else as such,
    and refuses for a full queue only when 512 commands are pending. [abort();
    not confirmed in the binary]
    (i) After each operation, the session has acknowledged each desk data frame
    owed an acknowledgement once each time it came, and no other frame.
    [abort(); not confirmed in the binary]
    (j) After each operation, a wake frame went exactly when the host woke and a
    close frame exactly when owed; each desk data frame but a keepalive or a
    repeat, each announce and each foreign session was noticed as owed; and the
    state changed exactly as the header diagram says, in order, each change
    naming its reason. [abort(); not confirmed in the binary]
    (k) After each operation, an acknowledgement of the frame in flight was
    taken and noticed, a frame in flight still unacknowledged after the timeout
    was sent again or dropped, and the reported deadline is from now to one
    second away and never later than the next retransmission. [abort(); not
    confirmed in the binary]
    (l) After each operation, with tagged commands, a keepalive due while online
    with nothing in flight and no back-off holding has gone: never skipped.
    [abort(); not confirmed in the binary]
    (m) With tagged commands, after each operation the queue holds exactly the
    pending commands in order, a newer command in its key place, and after a
    tick a command that may go has gone. [abort(); not confirmed in the binary]
    Only the checks marked ''confirmed in the binary'' had their assertion text
    or message found in the binary's bytes; for the others no usable text was
    found, which does not mean that they are compiled out, and no statement
    below relies on them.

    Whether each statement is open, proved or known false is recorded in the
    harness README, not here: this file changes only when a statement does. *)

From Stdlib Require Import QArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libdiginet.fuzz_transport Require Images.

(** ** Halting *)

(** On every input on which the plain build is never refused memory for
    exceeding 16 GiB, and when the environment refuses nothing it is not forced
    to, every execution of the plain build exits with status 0 or 2.  It never
    crashes, fails an assertion, hangs, or leaves the model.

    Not claimed: anything about what the program writes; anything about other
    compilers, architectures or libdiginet commits. *)
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
    instruments (the harness, libdiginet and the driver, less the code the
    harness README lists as uninstrumented).

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
    harness, libdiginet and the driver, less the code the harness README lists
    as uninstrumented). *)
Definition asan_ubsan_agrees : Prop :=
  agrees_in Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan_ubsan.

(** ** Proving a statement

    A proof is a directory named after the statement, in this fuzz target's
    proofs folder (docs/proving.md says where it is), whose Proof.v ends, for
    example, in
      Theorem plain_halts_holds : Statements.plain_halts.

    See docs/proving.md. *)
