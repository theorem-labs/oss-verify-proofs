(** * reac-pw / fuzz_segconf: theorem statements

    SUBJECT.  Four builds of reac-pw's own fuzz target [fuzz_segconf], which
    OSS-Fuzz does not run, for reac-pw 1.0.42 (FreeREAC/reac-pw at f86a30a3),
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

    WHAT THE HARNESS CHECKS.  Reads one to four operator configuration texts
    made from the input (drop-in files under fuzz-chosen labels, then the main
    file) with the configuration reader, then compares every segment, role,
    model, ignore switch, provenance, refusal and declared VLAN with what the
    harness predicts from its own reading of the documented grammar, checks that
    a `knock` line is refused with its reason, and probes names no section
    opened.  The harness checks:
    (a) The segments listed are the names the sections opened, each once, in the
    order first opened, with any past the 32-segment bound counted as overflow,
    as the harness's own line-by-line reading of the files predicts. [abort();
    not confirmed in the binary]
    (b) Each segment's role is the last one its files pinned, after the rule
    that a box with no model falls back to auto, as the harness's reading
    predicts. [abort(); not confirmed in the binary]
    (c) Each segment's model is a token of the box-model table folded to lower
    case, kept only on a segment whose role is box. [abort(); not confirmed in
    the binary]
    (d) A segment is switched off exactly when the last file to say ignore said
    yes, true or 1. [abort(); not confirmed in the binary]
    (e) The role and the ignore answer of each segment name the file that gave
    them. [abort(); not confirmed in the binary]
    (f) A kept refusal of a `knock` line, whatever its value, says that the
    knock takes no plan. [abort(); not confirmed in the binary]
    (g) Every line the grammar cannot use is refused and counted, and the first
    ones (up to the kept bound) are kept. [abort(); not confirmed in the binary]
    (h) Each kept refusal starts with its address: the file and the line, or the
    file alone for a rule that needed every file read. [abort(); not confirmed
    in the binary]
    (i) A name no section opened has no entry and no role, ignore or model
    answer, for each opened name with one byte added and for the fixed name
    nosuch0 when no section opened it. [abort(); not confirmed in the binary]
    (j) The declared VLANs are the segments named parent.vid that are not
    switched off, with a valid VLAN id, each once and within the table capacity
    given. [abort(); not confirmed in the binary]
    Only the checks marked ''confirmed in the binary'' had their assertion text
    or message found in the binary's bytes; for the others no usable text was
    found, which does not mean that they are compiled out, and no statement
    below relies on them.

    Whether each statement is open, proved or known false is recorded in the
    harness README, not here: this file changes only when a statement does. *)

From Stdlib Require Import QArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_pw.fuzz_segconf Require Images.

(** ** Halting *)

(** On every input on which the plain build is never refused memory for
    exceeding 16 GiB, and when the environment refuses nothing it is not forced
    to, every execution of the plain build exits with status 0 or 2.  It never
    crashes, fails an assertion, hangs, or leaves the model.

    Not claimed: anything about what the program writes; anything about other
    compilers, architectures or reac-pw commits. *)
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
    instruments (the harness, reac-pw and the driver, less the code the harness
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
    harness, reac-pw and the driver, less the code the harness README lists as
    uninstrumented). *)
Definition asan_ubsan_agrees : Prop :=
  agrees_in Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan_ubsan.

(** ** Proving a statement

    A proof is a directory named after the statement, in this fuzz target's
    proofs folder (docs/proving.md says where it is), whose Proof.v ends, for
    example, in
      Theorem plain_halts_holds : Statements.plain_halts.

    See docs/proving.md. *)
