(** * toy / exit0: theorem statements

    SUBJECT.  Two static riscv64 Linux programs written for this repository
    (tests/toy/make_elf.py), in the roles a harness's builds play:
      plain   132 bytes: three instructions that call exit_group(0)
      padded  136 bytes: the same program with a no-op in front
    Their statements have the same shapes as every harness's, and
    tests/proofs/toy/exit0/ proves each of them, so they are the smallest
    end-to-end example of a statement, a proof and the check CI runs on it
    (tests/check.sh).

    All three are true: both programs exit with status 0 from every entry, on
    every input, whatever the environment does, and write nothing. *)

From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.exit0 Require Images.

(** On every input on which [plain] is never refused memory for exceeding
    16 GiB, and when the environment refuses nothing it is not forced to,
    every execution exits with status 0 or 2. *)
Definition plain_halts : Prop :=
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused Images.plain.

(** Every execution of [plain] exits, with any status, on every input and
    whatever the environment refuses. *)
Definition plain_halts_may_fail : Prop :=
  halts_may_fail Exits.any Images.plain.

(** [plain] and [padded] agree, in the sense a sanitizer build must agree
    with its plain build: neither ever reaches an error, and both have the
    same traces (here: exit_group(0) and nothing else). *)
Definition padded_agrees : Prop :=
  agrees Budgets.Standard.lim_source Budgets.Standard.lim_target Images.plain Images.padded.
