From OSSVerify.plugin_hostd.fuzz_command Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Theorems.

Theorem asan_ubsan_halts_holds : OSSVerify.plugin_hostd.fuzz_command.Statements.asan_ubsan_halts.
Proof. exact OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Theorems.plugin_hostd_fuzz_command_asan_ubsan_halts. Qed.
