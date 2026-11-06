(** * plugin-hostd / fuzz_command: theorem statements

    SUBJECT.  Four builds of plugin-hostd's own fuzz target [fuzz_command],
    which OSS-Fuzz does not run, for plugin-hostd 0.10.0 (FreeMixer/plugin-hostd
    at 65cd2b02), static riscv64 Linux programs run as [<file> FILE]:
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

    WHAT THE HARNESS CHECKS.  Reads the input as up to 32 messages, each a flags
    byte, a two-byte length and up to 8192 bytes, copies each into an allocation
    of exactly its length and hands it to verbs_receive, plugin-hostd's command
    parser and dispatcher. A recorder stands in for the supervisor, the pins,
    the descriptor scans and the socket: it records every call and, as the flags
    byte chooses, accepts it with the verb's declared reply or refuses it with a
    declared error code. After each message the harness checks the reply and the
    calls, then sends the message again as its words joined by one space.  The
    harness checks:
    (a) Every message gets exactly one reply, a NUL-terminated string with no
    earlier NUL. When a recorded call answered, the reply is that answer
    unchanged; otherwise it is a refusal or the ''resp 0'' of quit. A refusal is
    ''resp <code>'' of a declared error code, and any other reply has the shape
    its verb declares or mod-host's ''resp 0''. [abort(); not confirmed in the
    binary]
    (b) A verb the daemon parses itself (its own verbs, and mod-host's remove,
    connect, disconnect and quit) is acted on only with an argument count its
    declared syntax allows, counting at most 64 words; a line passed on to every
    worker for the workers to refuse is exempt. [abort(); not confirmed in the
    binary]
    (c) Each recorded call gets the message's words where the verb's declaration
    puts them (as written, as atoi reads them, or the whole line with single
    spaces), and add's placement and client, chain's members and their count,
    and pin_set's verdict are the ones the harness works out from the words.
    Other arguments are not checked. [abort(); not confirmed in the binary]
    (d) A refused command (a reply with a negative code) leaves the recorded
    state as it was: no accepted call, no descriptor scan or other follow-up,
    and no quit. [abort(); not confirmed in the binary]
    (e) A command the daemon acted on, sent again from the same state as its
    words joined by one space, makes the same calls with the same arguments, the
    same reply, the same state and host settings, and quits the same. [abort();
    not confirmed in the binary]
    (f) The reply shape each verb declares, filled in, fits one line of the
    protocol (4096 bytes). [abort(); not confirmed in the binary]
    Only the checks marked ''confirmed in the binary'' had their assertion text
    or message found in the binary's bytes; for the others no usable text was
    found, which does not mean that they are compiled out, and no statement
    below relies on them.

    Whether each statement is open, proved or known false is recorded in the
    harness README, not here: this file changes only when a statement does. *)

From Stdlib Require Import QArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.plugin_hostd.fuzz_command Require Images.

(** ** Halting *)

(** On every input on which the plain build is never refused memory for
    exceeding 16 GiB, and when the environment refuses nothing it is not forced
    to, every execution of the plain build exits with status 0 or 2.  It never
    crashes, fails an assertion, hangs, or leaves the model.

    Not claimed: anything about what the program writes; anything about other
    compilers, architectures or plugin-hostd commits. *)
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
    instruments (the harness, plugin-hostd and the driver, less the code the
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
    harness, plugin-hostd and the driver, less the code the harness README lists
    as uninstrumented). *)
Definition asan_ubsan_agrees : Prop :=
  agrees_in Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan_ubsan.

(** ** Proving a statement

    A proof is a directory named after the statement, in this fuzz target's
    proofs folder (docs/proving.md says where it is), whose Proof.v ends, for
    example, in
      Theorem plain_halts_holds : Statements.plain_halts.

    See docs/proving.md. *)
