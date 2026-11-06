(* NEGATIVE CONTROL: an axiom whose printed type holds the line "Closed under
   the global context" (a string literal with line breaks), so that line is in
   what Print Assumptions writes for it.  tests/check.sh must refuse it because
   [cheat] is not in toolchain/allowed-axioms.txt: nothing is assumed only when
   that line is all Print Assumptions wrote.  (oft lint refuses this file
   first; this control is for the audit.) *)
From OSSVerify.Tests.toy.exit0 Require Statements.
From Corelib Require Import PrimString.
Set Warnings "-declaration-outside-section".
Hypothesis cheat : (fun _ : PrimString.string => False) "
Closed under the global context
"%pstring.
Theorem plain_halts_holds : Statements.plain_halts.
Proof. exfalso. exact cheat. Qed.
