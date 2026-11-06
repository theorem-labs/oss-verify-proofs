(** * reac-repacer / fuzz_wire: theorem statements

    SUBJECT.  Four builds of reac-repacer's own fuzz target [fuzz_wire], which
    OSS-Fuzz does not run, for reac-repacer 0.2.3 (FreeREAC/reac-repacer at
    3ac1cf10), static riscv64 Linux programs run as [<file> FILE]:
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

    WHAT THE HARNESS CHECKS.  Takes one flag byte (the broadcast-only switch and
    a channel slot from -2 to 125) and then a frame, cut to the 1600 bytes of
    the daemon's receive buffer. It runs the frame through every reader the
    daemon applies to a frame from the wire: the forward classifier, the return
    relay, the downstream listener, the clock meter, the counter read, the
    channel-width rule, the tag-removing copy reader and the slot sample reader.
    It compares each answer with one the harness computes itself from the REAC
    frame layout.  The harness checks:
    (a) The forward reader queues a REAC frame of 18 bytes or more (with
    broadcast-only, only one whose destination starts with 0xff) as audio when
    its type is 00 00 and as control otherwise, and drops every other frame.
    [abort(); not confirmed in the binary]
    (b) The return relay passes exactly the REAC frames of 14 bytes or more.
    [abort(); not confirmed in the binary]
    (c) The downstream listener accepts exactly the REAC frames of 18 bytes or
    more, untagged or behind one 802.1Q VLAN tag. [abort(); not confirmed in the
    binary]
    (d) The clock meter counts exactly the REAC frames of 1000 bytes or more,
    untagged or tagged, reads the frame counter as the two little-endian bytes
    after the EtherType, and leaves the counter unchanged for a frame it skips.
    [abort(); not confirmed in the binary]
    (e) For a frame of 18 bytes or more, the counter read is bytes 14-15,
    little-endian. [abort(); not confirmed in the binary]
    (f) The channel width of a frame length is the frame law's (52 bytes plus 36
    per channel, for an even width from 2 to 40, or 2 bytes more with an FCS
    residue), and no negative length has a width. [abort(); not confirmed in the
    binary]
    (g) The copy reader keeps exactly the REAC audio frames of 50 bytes or more;
    a tagged one loses its four tag bytes and nothing else moves. [abort(); not
    confirmed in the binary]
    (h) A slot is read only when the frame is audio and its width holds the
    slot; the 12 samples read are the ones the REAC braid layout places there,
    sign-extended from 24 bits; a declined read leaves the samples unchanged.
    [abort(); not confirmed in the binary]
    Only the checks marked ''confirmed in the binary'' had their assertion text
    or message found in the binary's bytes; for the others no usable text was
    found, which does not mean that they are compiled out, and no statement
    below relies on them.

    Whether each statement is open, proved or known false is recorded in the
    harness README, not here: this file changes only when a statement does. *)

From Stdlib Require Import QArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_repacer.fuzz_wire Require Images.

(** ** Halting *)

(** On every input on which the plain build is never refused memory for
    exceeding 16 GiB, and when the environment refuses nothing it is not forced
    to, every execution of the plain build exits with status 0 or 2.  It never
    crashes, fails an assertion, hangs, or leaves the model.

    Not claimed: anything about what the program writes; anything about other
    compilers, architectures or reac-repacer commits. *)
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
    instruments (the harness, reac-repacer and the driver, less the code the
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
    harness, reac-repacer and the driver, less the code the harness README lists
    as uninstrumented). *)
Definition asan_ubsan_agrees : Prop :=
  agrees_in Env.alloc_forced_only Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan_ubsan.

(** ** Proving a statement

    A proof is a directory named after the statement, in this fuzz target's
    proofs folder (docs/proving.md says where it is), whose Proof.v ends, for
    example, in
      Theorem plain_halts_holds : Statements.plain_halts.

    See docs/proving.md. *)
