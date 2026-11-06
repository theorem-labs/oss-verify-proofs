(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: added for this unit's ASan statements: it prints the type and the assumptions of
   each proof term the statement directories export, so that one build records both. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Theorems.

Check OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Theorems.plugin_hostd_fuzz_command_asan_agrees.
Print Assumptions OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Theorems.plugin_hostd_fuzz_command_asan_agrees.
Check OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Theorems.plugin_hostd_fuzz_command_asan_halts.
Print Assumptions OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Theorems.plugin_hostd_fuzz_command_asan_halts.
