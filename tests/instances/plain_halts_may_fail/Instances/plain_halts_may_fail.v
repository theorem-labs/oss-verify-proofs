(** POSITIVE CONTROL: the instance of toy/exit0/plain_halts_may_fail.  Its
    file, wrong-argc.bin, is empty, and its path is refused-by-driver: argv is
    ["exit0"], so the driver would exit 2 and not read the file, which the
    input holds as "input.bin".  On that input the premises of
    [halts_may_fail] hold together: a valid entry and a valid input. *)
From Stdlib Require Import List.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Tests.toy.exit0 Require Images.
From OSSVerify.Tests.proofs.lib Require Import Exit0Instance.
Import ListNotations.

Lemma plain_halts_may_fail_instance :
  exists en, valid_entry Images.plain en (input refused_by_driver [])
    /\ valid_input (input refused_by_driver []).
Proof. exact (halts_may_fail_premises _ _ launch_argv_refused_by_driver). Qed.
