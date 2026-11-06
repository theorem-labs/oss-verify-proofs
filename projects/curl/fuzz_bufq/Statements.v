(** * curl / fuzz_bufq: theorem statements

    SUBJECT.  Four builds of curl's own fuzz target [fuzz_bufq], as OSS-Fuzz
    builds it, for curl (curl/curl at f190aa8e), static riscv64 Linux programs
    run as [<file> FILE]:
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

    WHAT THE HARNESS CHECKS.  Runs a fuzzer-chosen sequence of operations on one
    curl byte queue (bufq) and checks it with 12 asserts (listed below): the
    bytes read, peeked and passed follow the 0..255 pattern written, the queue's
    length and emptiness match the harness's byte count before each operation,
    and the count stays within the capacity after each write, slurp and sipn.
    The harness checks:
    (a) Each piece Curl_bufq_pass hands its writer callback, up to the bytes the
    pass still asks for, follows the 0..255 pattern from the next byte to read
    (upstream line 94). The pattern repeats every 256 bytes. [assert();
    confirmed in the binary]
    (b) Before each operation, Curl_bufq_is_empty is true exactly when the
    harness's count of queued bytes is 0 (upstream line 169). [assert();
    confirmed in the binary]
    (c) Before each operation, Curl_bufq_len equals the harness's count of
    queued bytes (upstream line 170). [assert(); confirmed in the binary]
    (d) The bytes Curl_bufq_peek returns follow the pattern from the next byte
    to read (upstream line 188). The pattern repeats every 256 bytes. [assert();
    confirmed in the binary]
    (e) The bytes Curl_bufq_peek_at returns at an offset follow the pattern from
    that offset (upstream line 203). The pattern repeats every 256 bytes.
    [assert(); confirmed in the binary]
    (f) Always true: buffer_bytes >= 0 after a read, where buffer_bytes is a
    size_t (upstream line 219). The compiler removes it: its text is in none of
    the four binaries. No change to curl can make it fail. [assert(); compiled
    out]
    (g) The bytes Curl_bufq_read copies out follow the pattern from the next
    byte to read (upstream line 222). The pattern repeats every 256 bytes.
    [assert(); confirmed in the binary]
    (h) After Curl_bufq_slurp, the harness's count of queued bytes is at most
    chunk_size * max_chunks (upstream line 244). [assert(); confirmed in the
    binary]
    (i) After a successful Curl_bufq_sipn, the count is at most chunk_size *
    max_chunks (upstream line 258). [assert(); confirmed in the binary]
    (j) Always true: buffer_bytes >= 0 after a pass, where buffer_bytes is a
    size_t (upstream line 280). The compiler removes it: its text is in none of
    the four binaries. No change to curl can make it fail. [assert(); compiled
    out]
    (k) After a successful Curl_bufq_write, the count is at most chunk_size *
    max_chunks (upstream line 305). [assert(); confirmed in the binary]
    (l) Never reached: assert(false) in the switch default (upstream line 314),
    but op_type is in 0..8 and each value has a case. The plain and ASan builds
    drop it; the UBSan and ASan+UBSan builds keep it, so it is neither live nor
    compiled out in all four. No change to curl can make it fail. [assert(); not
    confirmed in the binary]
    Only the checks marked ''confirmed in the binary'' had their assertion text
    or message found in the binary's bytes; for the others no usable text was
    found, which does not mean that they are compiled out, and no statement
    below relies on them.

    Whether each statement is open, proved or known false is recorded in the
    harness README, not here: this file changes only when a statement does. *)

From Stdlib Require Import QArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.curl.fuzz_bufq Require Images Distribution.

(** ** Halting *)

(** On every input on which the plain build is never refused memory for
    exceeding 16 GiB, and when the environment refuses nothing it is not forced
    to, every execution of the plain build exits with status 0 or 2.  It never
    crashes, fails an assertion, hangs, or leaves the model.  Checks (a), (b),
    (c), (d), (e), (g), (h), (i) and (k) each end the process when they fail,
    which this statement excludes, so a proof establishes them for the code in
    this binary on every input it covers.

    Not claimed: anything about what the program writes; anything about other
    compilers, architectures or curl commits. *)
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
    exceeding 2 GiB, whatever the environment refuses in either build: neither
    build ever faults, aborts or leaves the model, and the two write the same
    bytes and exit with the same status.  An ASan report aborts, so a proof
    shows that ASan reports nothing on any such input: no memory error that this
    build's ASan detects happens in the code it instruments (the harness, curl
    and the driver, less the code the harness README lists as uninstrumented).
    Stated with abort() read as death by SIGABRT rather than as a step the model
    does not cover; the statement still forbids it.

    Not claimed: anything about inputs on which the plain build needs more than
    2 GiB; memory errors ASan does not detect (for example an access that lands
    inside another live object, or one made in code it does not instrument). *)
Definition asan_agrees : Prop :=
  agrees_abort_modelled Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan.

(** As [asan_agrees], for the UBSan build, with 16 GiB for the plain build.  A
    failed UBSan check traps, so a proof shows that no UBSan check in this build
    fails on any such input.  Stated with abort() read as death by SIGABRT
    rather than as a step the model does not cover; the statement still forbids
    it. *)
Definition ubsan_agrees : Prop :=
  agrees_abort_modelled Budgets.Standard.lim_source Budgets.Standard.lim_target Images.plain Images.ubsan.

(** As [asan_agrees], for the ASan+UBSan build, with 2 GiB for the plain build.
    An ASan report aborts and a failed UBSan check traps, so a proof shows that
    neither sanitizer fires on any such input in the code they instrument (the
    harness, curl and the driver, less the code the harness README lists as
    uninstrumented).  Stated with abort() read as death by SIGABRT rather than
    as a step the model does not cover; the statement still forbids it. *)
Definition asan_ubsan_agrees : Prop :=
  agrees_abort_modelled Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan_ubsan.

(** ** How often the builds disagree *)

(** For an input drawn from [Distribution.w] (Distribution.v), the probability
    that the plain and ASan builds are not both error-free with equal traces is
    at most [b].  Agreement here is judged at 16 GiB / 512 GiB with no budget
    premise (Core.Shapes), so [asan_agrees] does not by itself give
    [asan_disagrees_at_most 0].  Smaller [b] is stronger; [b = 1] holds
    trivially. *)
Definition asan_disagrees_at_most (b : Q) : Prop :=
  disagrees_at_most Env.may_fail Distribution.w Distribution.M Images.plain Images.asan b.

(** As [asan_disagrees_at_most], for the UBSan build. *)
Definition ubsan_disagrees_at_most (b : Q) : Prop :=
  disagrees_at_most Env.may_fail Distribution.w Distribution.M Images.plain Images.ubsan b.

(** As [asan_disagrees_at_most], for the ASan+UBSan build. *)
Definition asan_ubsan_disagrees_at_most (b : Q) : Prop :=
  disagrees_at_most Env.may_fail Distribution.w Distribution.M Images.plain Images.asan_ubsan b.

(** ** Deciding where the builds agree *)

(** Some well-formed riscv64 program decides exactly the finite inputs on which
    the plain and ASan builds agree ([Characterise.v] states the problem for a
    given program). *)
Definition asan_agreement_decidable : Prop :=
  agreement_decidable Env.may_fail Images.plain Images.asan.

(** As [asan_agreement_decidable], for the UBSan build. *)
Definition ubsan_agreement_decidable : Prop :=
  agreement_decidable Env.may_fail Images.plain Images.ubsan.

(** As [asan_agreement_decidable], for the ASan+UBSan build. *)
Definition asan_ubsan_agreement_decidable : Prop :=
  agreement_decidable Env.may_fail Images.plain Images.asan_ubsan.

(** ** Proving a statement

    A proof is a directory named after the statement, in this fuzz target's
    proofs folder (docs/proving.md says where it is), whose Proof.v ends, for
    example, in
      Theorem plain_halts_holds : Statements.plain_halts.
    A bound proof names its bound:
      Theorem asan_disagrees_at_most_holds : Statements.asan_disagrees_at_most (1 # 1000).
    See docs/proving.md. *)
