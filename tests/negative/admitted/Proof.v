(* NEGATIVE CONTROL: a proof that is not finished.  [Admitted] makes the
   theorem an axiom; tests/check.sh must refuse it because that axiom is not
   in toolchain/allowed-axioms.txt. *)
From OSSVerify.Tests.toy.exit0 Require Statements.
Theorem plain_halts_holds : Statements.plain_halts.
Proof.
Admitted.
