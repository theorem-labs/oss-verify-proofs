(** * omx-clap-core / fuzz_manifest: theorem statements

    SUBJECT.  Four builds of omx-clap-core's own fuzz target [fuzz_manifest],
    which OSS-Fuzz does not run, for omx-clap-core 0.20.1
    (FreeMixer/omx-clap-core at 246923f0), static riscv64 Linux programs run as
    [<file> FILE]:
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

    WHAT THE HARNESS CHECKS.  Splits the input into a plugin URI (a length byte,
    then that many bytes) and the text of an LV2 bundle's manifest.ttl (the
    rest, at most 4 MiB), each up to its first NUL, and asks
    lv2_locate_manifest_names whether the manifest names the URI, checking the
    answer against the harness's own reading of the rule the header states
    (''<uri>'', or an @prefix or PREFIX namespace and a prefixed name as a whole
    token). It then asks again with the allocation failing, and asks of
    manifests the harness writes from the URI itself.  The harness checks:
    (a) The manifest and URI followed after their NUL by a name character or by
    NULs get the same answer: the reader reads nothing past either string.
    [abort(); not confirmed in the binary]
    (b) The reader holds at most the URI's length plus 3 bytes. [abort(); not
    confirmed in the binary]
    (c) The reader says the manifest names the URI exactly when the harness's
    own reading of the stated rule does, including the limit of 16 namespace
    declarations read. [abort(); not confirmed in the binary]
    (d) Whatever the answer, the reader gives back every byte it allocated, also
    when asked with its allocation failing. [abort(); not confirmed in the
    binary]
    (e) The empty text names nothing; a manifest written from the URI as
    ''<uri>'', and at each split into a namespace and a plain local name as an
    @prefix, a SPARQL PREFIX or an empty-prefix declaration with its prefixed
    name, names it; the same spellings with one more name character answer as
    the rule says. [abort(); not confirmed in the binary]
    Only the checks marked ''confirmed in the binary'' had their assertion text
    or message found in the binary's bytes; for the others no usable text was
    found, which does not mean that they are compiled out, and no statement
    below relies on them.

    Whether each statement is open, proved or known false is recorded in the
    harness README, not here: this file changes only when a statement does. *)

From Stdlib Require Import QArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_manifest Require Images.

(** ** Halting *)

(** On every input on which the plain build is never refused memory for
    exceeding 16 GiB, and when the environment refuses nothing it is not forced
    to, every execution of the plain build exits with status 0 or 2.  It never
    crashes, fails an assertion, hangs, or leaves the model.

    Not claimed: anything about what the program writes; anything about other
    compilers, architectures or omx-clap-core commits. *)
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
    instruments (the harness, omx-clap-core and the driver, less the code the
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
    harness, omx-clap-core and the driver, less the code the harness README
    lists as uninstrumented). *)
Definition asan_ubsan_agrees : Prop :=
  agrees_in Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan_ubsan.

(** ** Proving a statement

    A proof is a directory named after the statement, in this fuzz target's
    proofs folder (docs/proving.md says where it is), whose Proof.v ends, for
    example, in
      Theorem plain_halts_holds : Statements.plain_halts.

    See docs/proving.md. *)
