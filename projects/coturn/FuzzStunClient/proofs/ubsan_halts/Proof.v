From OSSVerify.coturn.FuzzStunClient Require Statements.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Corpus Require Halts.

Theorem ubsan_halts_holds : OSSVerify.coturn.FuzzStunClient.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.coturn.FuzzStunClient.lib.Corpus.Halts.coturn_fuzzstunclient_ubsan_halts. Qed.
