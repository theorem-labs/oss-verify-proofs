(* SPDX-License-Identifier: MIT *)
(** Exact original zlib halting statement, from the actual complete fuzzer and driver certificates. *)
From OssFuzzTheorems.zlib.checksum_fuzzer Require Statements.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib Require Import ZValidChecksum.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import DriverValid.
Theorem plain_halts_holds : Statements.plain_halts.
Proof.
  apply plain_halts_from_valid_checksum.
  intros rc fx. apply checksum_valid_contract.
Qed.
