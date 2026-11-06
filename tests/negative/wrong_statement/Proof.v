(* NEGATIVE CONTROL: a finished, axiom-free proof of a DIFFERENT statement,
   under the name the claimed one expects.  tests/check.sh must refuse it
   because the wrapper it writes ascribes the theorem to the claimed
   statement's type, and plain_halts_may_fail is not plain_halts. *)
From OSSVerify.Tests.toy.exit0 Require Statements.
From OSSVerify.Tests.proofs.toy.exit0.plain_halts_may_fail Require Proof.
Theorem plain_halts_holds : Statements.plain_halts_may_fail.
Proof. exact Proof.plain_halts_may_fail_holds. Qed.
