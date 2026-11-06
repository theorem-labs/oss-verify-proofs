(* NEGATIVE CONTROL, part 2: an axiom-free proof of the doctored statement. *)
From OSSVerify.Tests.toy.exit0 Require Statements.
Theorem plain_halts_holds : Statements.plain_halts.
Proof. exact I. Qed.
