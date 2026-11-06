(** * RefLim: the plain build's allocation budget, as a class.

    The plain image runs at [SanitizerBudgets.lim_source] (2 GiB) in the asan and asan-ubsan pairs and at
    [ShippedBudgets.lim_source] (16 GiB) in the ubsan pair.  The plain realization ([RefMain]) is proved once over
    any budget [LIM] with [2 ^ 31 <= LIM]: a plain run's live heap never exceeds 1,141,911,552 bytes (the
    target-phase entry ledger, read buffer included, plus one grant of at most 2 ^ 30 bytes), so every grant side
    condition holds at 2 GiB.  No instance is declared: each use names its budget. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.

Class AllocLim : Type := ALLOC_LIM {
  LIM : Z;
  LIM_ge : (2 ^ 31 <= LIM)%Z
}.

Definition SrcLim : AllocLim := ALLOC_LIM source_alloc_limit ltac:(apply Z.leb_le; reflexivity).
Definition SanLim : AllocLim := ALLOC_LIM SanitizerBudgets.lim_source ltac:(apply Z.leb_le; reflexivity).
