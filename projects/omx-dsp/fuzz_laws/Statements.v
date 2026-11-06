(** * omx-dsp / fuzz_laws: theorem statements

    SUBJECT.  Four builds of omx-dsp's own fuzz target [fuzz_laws], which
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

    WHAT THE HARNESS CHECKS.  Reads up to 64 calls, each picked by a selector
    byte. Its arguments are raw float words where a law takes any value,
    two-byte values mapped onto a law's travel, selector bytes (block lengths,
    pan leg, rate) and single bits (mutes). The calls cover the clamps and unit
    knob, dB to linear and back in both forms, the pan and balance laws, the
    fader coefficient, the linear ramp, the wet/dry mix and cross-fade, and the
    one-pole constructors, rescale and step. Each result is checked against its
    law, and the contract ledger is read after each call.  The harness checks:
    (a) omx_clampf, omx_clamp_or and omx_unit land inside their travel for any
    word. A word already inside comes back unchanged, and a non-finite word
    given to omx_clamp_or reads as the declared default. [abort(); not confirmed
    in the binary]
    (b) dB to linear is never negative and, inside +-150 dB, finite and
    positive, in both the libm and polynomial forms. Linear to dB keeps its
    floor and stays finite for any finite word; the polynomial form stays
    finite. [abort(); not confirmed in the binary]
    (c) Inside +-150 dB, converting dB to linear and back gives the original dB
    to within 0.01 dB. [abort(); not confirmed in the binary]
    (d) The pan law is constant power: the squares of the two legs add up to 1
    (to 1e-5) on [-1, 1]. [abort(); not confirmed in the binary]
    (e) The balance law never boosts: both legs are in [0, 1] and one of them is
    1, at any pan word. The fader coefficient is finite and not negative, and 0
    when the strip or the DCA is muted, for a fader level on a 16-bit grid of
    [-200, 60] dB and send and DCA gains capped at 1e6. [abort(); not confirmed
    in the binary]
    (f) A ramp starts at the applied value (0 when that is not finite), never
    leaves the span of its two ends, and ends on its target. [abort(); not
    confirmed in the binary]
    (g) For samples on a 16-bit grid of [-8, 8], the wet/dry mix lies between
    the dry and wet samples, to 1e-5. For bodies on a 16-bit grid of [-4, 4],
    each cross-fade sample lies between the outgoing and incoming bodies, to
    1e-5. [abort(); not confirmed in the binary]
    (h) The time and corner constructors give a pole in [0, 1) for any finite
    argument, and a rescaled pole stays in [0, 1]. For a state and an input on a
    16-bit grid of [-4, 4], one filter step lies between the input and the state
    (to 1e-5), and the step returns the new state. [abort(); not confirmed in
    the binary]
    (i) After each call, no contract of the library is recorded as broken,
    except the crossover token bands-partition-unity, which this harness never
    reaches. [abort(); not confirmed in the binary]
    Only the checks marked ''confirmed in the binary'' had their assertion text
    or message found in the binary's bytes; for the others no usable text was
    found, which does not mean that they are compiled out, and no statement
    below relies on them.

    Whether each statement is open, proved or known false is recorded in the
    harness README, not here: this file changes only when a statement does. *)

From Stdlib Require Import QArith.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_dsp.fuzz_laws Require Images.

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
