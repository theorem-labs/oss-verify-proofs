From OSSVerify.plugin_hostd.fuzz_reply Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require SlotAll.

Theorem plain_halts_holds : Statements.plain_halts.
Proof. exact SlotAll.plain_halts_of_parts. Qed.
