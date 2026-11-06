(** * toy / exit1: theorem statements

    SUBJECT.  The [exit0] toy with one immediate changed
    (tests/toy/make_elf.py): it calls exit_group(1).  [plain_halts] is FALSE
    for it, because 1 is not an allowed status, and
    tests/proofs/toy/exit1/plain_halts/Refutation.v proves so.  It is the
    control that says a halts statement is not satisfied by every program
    that halts. *)

From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.exit1 Require Images.

Definition plain_halts : Prop :=
  halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused Images.plain.

Definition plain_halts_may_fail : Prop :=
  halts_may_fail Exits.any Images.plain.
