(* NEGATIVE CONTROL: a proof that hides the axiom it needs from the audit.
   [cheat] is a Hypothesis outside any Section, so an axiom of this file, and
   the theorem's deprecation note makes Rocq print "Closed under the global
   context" wherever the theorem is used, the wrapper's compile included (the
   Verified Linux team's report, 2026-10-29).  tests/check.sh must refuse it
   because [cheat] is not in toolchain/allowed-axioms.txt: it reads only the
   file Print Assumptions writes.  (oft lint refuses this file first; this
   control is for the audit.) *)
From OSSVerify.Tests.toy.exit0 Require Statements.
Set Warnings "-declaration-outside-section".
Hypothesis cheat : False.
#[deprecated(since="payload", note="
Closed under the global context
")]
Theorem plain_halts_holds : Statements.plain_halts.
Proof. destruct cheat. Qed.
