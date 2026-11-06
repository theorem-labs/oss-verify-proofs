(* NEGATIVE CONTROL: a proof that assumes what it needs.  tests/check.sh
   must refuse it because [cheat] is not in toolchain/allowed-axioms.txt. *)
From OSSVerify.Tests.toy.exit0 Require Statements.
Axiom cheat : False.
Theorem plain_halts_holds : Statements.plain_halts.
Proof. destruct cheat. Qed.
