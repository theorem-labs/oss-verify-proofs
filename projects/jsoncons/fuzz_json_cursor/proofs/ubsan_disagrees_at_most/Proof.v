From Stdlib Require Import QArith.
From OSSVerify.jsoncons.fuzz_json_cursor Require Statements.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require ConstAccept.

Theorem ubsan_disagrees_at_most_holds : OSSVerify.jsoncons.fuzz_json_cursor.Statements.ubsan_disagrees_at_most 0.
Proof. exact OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.ConstAccept.ubsan_bound_0. Qed.
