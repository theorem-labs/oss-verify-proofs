From OSSVerify.msgpack_c.unpack_pack_fuzzer Require Statements.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require Theorems.

Theorem asan_halts_holds : OSSVerify.msgpack_c.unpack_pack_fuzzer.Statements.asan_halts.
Proof. exact OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Theorems.halts_allowed_msgpack_c_unpack_pack_fuzzer_halts_asan. Qed.
