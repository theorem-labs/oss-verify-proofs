From OSSVerify.plugin_hostd.fuzz_reply Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require AgreeReply.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof. exact AgreeReply.ubsan_agrees_holds. Qed.
