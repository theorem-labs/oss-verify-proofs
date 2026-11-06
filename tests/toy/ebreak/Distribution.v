(** * toy / ebreak: the input distribution of its bound statements

    Every input weighs 1 and the total mass is taken as 1.  A harness's
    Distribution.v has the same two names ([w], [M]); this one exists only
    so that the bound statements of Statements.v are written as the
    generator writes a harness's. *)
From Stdlib Require Import QArith.
From LinuxProcessSemantics.EquivalenceDefinition Require Import FinInput.

Definition w : FinProcInput -> Q := fun _ => 1%Q.
Definition M : Q := 1%Q.
