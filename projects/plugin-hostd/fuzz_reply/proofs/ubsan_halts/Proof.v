From OSSVerify.plugin_hostd.fuzz_reply Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require SlotAll.

Theorem ubsan_halts_holds : Statements.ubsan_halts.
Proof. exact SlotAll.ubsan_halts_of_parts. Qed.
