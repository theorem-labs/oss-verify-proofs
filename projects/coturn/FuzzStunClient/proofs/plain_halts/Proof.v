From OSSVerify.coturn.FuzzStunClient Require Statements.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Corpus Require Halts.

Theorem plain_halts_holds : OSSVerify.coturn.FuzzStunClient.Statements.plain_halts.
Proof. exact OSSVerify.Proofs.coturn.FuzzStunClient.lib.Corpus.Halts.coturn_fuzzstunclient_plain_halts. Qed.
