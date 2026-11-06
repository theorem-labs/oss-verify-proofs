From OSSVerify.msgpack_c.unpack_pack_fuzzer Require Statements.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require Theorems.

Theorem asan_agrees_holds : OSSVerify.msgpack_c.unpack_pack_fuzzer.Statements.asan_agrees.
Proof. exact OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Theorems.strong_universal_error_free_unpack_pack_fuzzer_asan. Qed.
