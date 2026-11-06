From OSSVerify.plugin_hostd.fuzz_command Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Theorems.

Theorem ubsan_halts_holds : OSSVerify.plugin_hostd.fuzz_command.Statements.ubsan_halts.
Proof. exact OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Theorems.plugin_hostd_fuzz_command_ubsan_halts. Qed.
