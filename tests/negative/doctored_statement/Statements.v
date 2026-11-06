(* NEGATIVE CONTROL, part 1: a doctored copy of
   tests/toy/exit0/Statements.v in which plain_halts says nothing.
   tests/check.sh compiles it in place of the real one, compiles Proof.v
   against it, and then checks Proof.v against the REAL statements, as CI
   does with statements built from the base branch.  Rocq must refuse to
   load a proof compiled against a different statements library. *)
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.exit0 Require Images.
Definition plain_halts : Prop := True.
Definition plain_halts_may_fail : Prop := halts_may_fail Exits.any Images.plain.
