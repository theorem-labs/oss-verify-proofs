(* NEGATIVE CONTROL: a lemma of the wrong type.  It proves the premises of
   halts_may_fail on the instance's input, which leave out the budget premise
   of plain_halts, under the name plain_halts expects, so the wrapper does not
   type-check. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Tests.toy.exit0 Require Images.
From OSSVerify.Tests.proofs.lib Require Import Exit0Instance.

Lemma plain_halts_instance :
  exists en, valid_entry Images.plain en (input reaches_harness seven)
    /\ valid_input (input reaches_harness seven).
Proof. exact (halts_may_fail_premises _ _ launch_argv_reaches_harness). Qed.
