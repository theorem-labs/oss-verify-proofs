(** * libreac / fuzz_ctrl: theorem statements

    SUBJECT.  Four builds of libreac's own fuzz target [fuzz_ctrl], which
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

    WHAT THE HARNESS CHECKS.  Reads the payload as our MAC, a mode byte and up
    to 256 length-prefixed frames, each in its own allocation, and runs every
    frame through libreac's control-plane parsers: reac_ctrl_parse, the checksum
    and head-amp record checks, the box classifier, the identity reply, the
    two-fragment identity reassembly and the catalogue match, and for a frame of
    at least 50 bytes with EtherType 0x8819 the port-table decode. When the mode
    byte asks, it first builds a catalogue row's blocks with reac_ctrl_build_as
    and parses them back.  The harness checks:
    (a) reac_ctrl_parse answers NONE exactly for a frame shorter than 50 bytes
    or not 0x8819, gives the same verdict with a NULL output, and its verdict is
    the kind it stores, which always has a name. [abort(); not confirmed in the
    binary]
    (b) The parser reads the addresses and counter where the frame holds them
    and calls a frame FILLER exactly for type 00 00; the block and head-amp
    record checksum checks agree with sums the harness computes, and a head-amp
    record is only a link-4 SINGLE. [abort(); not confirmed in the binary]
    (c) Both port decoders refuse the same blocks, leaving the output untouched;
    a decoded port table counts each slot code as its own kind in whole
    4-channel slots, accounts for all twelve slots, names the first unknown
    code, and gives the head-amp base from the chassis strap. [abort(); not
    confirmed in the binary]
    (d) An identity reply comes only from a frame with a closed block checksum,
    its payload lies where the record puts it inside the frame, its record
    checksum closes and its address is the record's own; a reassembled record
    lies inside the reassembly buffer, closes its checksum and carries the
    joined record's own address (its bytes 9 and 10), and a corrupt frame leaves
    the reassembly state unchanged. [abort(); not confirmed in the binary]
    (e) The box classifier answers only for a Roland-OUI source that is not us,
    with a closed block checksum outside FILLER, and with one of its six events;
    only a config-announce matches a catalogue row, and it is the first row
    whose declaration is the frame's block. [abort(); not confirmed in the
    binary]
    (f) Every block reac_ctrl_build_as emits for a catalogue row has a legal
    geometry and parses back as its kind; the config block's checksum closes, it
    is the row's declaration, the catalogue match recognises it and it declares
    the row's widths; its identity replies and reassembled records give the
    row's firmware, REAC version and, where the row has an identity record,
    model name. [abort(); not confirmed in the binary]
    (g) The catalogue is not empty, the documented refusals of a bad argument
    hold (NULL pointers are refused, reac_ports_unknown clears its code, an
    out-of-range kind is named ''?''), and an ingested model name is
    NUL-terminated. [abort(); not confirmed in the binary]
    Only the checks marked ''confirmed in the binary'' had their assertion text
    or message found in the binary's bytes; for the others no usable text was
    found, which does not mean that they are compiled out, and no statement
    below relies on them.

    Whether each statement is open, proved or known false is recorded in the
    harness README, not here: this file changes only when a statement does. *)

From Stdlib Require Import QArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_ctrl Require Images.

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
