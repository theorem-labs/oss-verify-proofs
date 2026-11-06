(* NEGATIVE CONTROL: a proof that uses an axiom of the standard library that
   is literally [False]: Stdlib.Compat.AdmitAxiom.proof_admitted.  It is
   installed with every Rocq, so an allowlist made of "every axiom of every
   installed library" admits this proof; toolchain/allowed-axioms.txt is the
   axioms of the statements' own closure, which does not contain it. *)
From Stdlib Require Import Compat.AdmitAxiom.
From OSSVerify.Tests.toy.exit0 Require Statements.
Theorem plain_halts_holds : Statements.plain_halts.
Proof. exfalso. exact proof_admitted. Qed.
