(** Development candidate for the exact second catalog statement.
    This file is not a successful proof until compiled and independently checked. *)
From OssFuzzTheorems.zlib.checksum_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail Require Import ZValidChecksum.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Checksum Require Import DriverValid.
Theorem plain_halts_may_fail_holds : Statements.plain_halts_may_fail.
Proof.
  apply plain_halts_may_fail_from_valid_checksum.
  intros rc fx. apply checksum_valid_contract.
Qed.
