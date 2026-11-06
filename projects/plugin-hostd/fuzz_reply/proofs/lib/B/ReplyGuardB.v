(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, the sink-instance guard of plugin-hostd/fuzz_reply's ASan+UBSan side
   (lib/B). lib/B states its sink arguments with the shared classes lib/Reusable/YI16.v sink_head and YI14.v sink_syms /
   sink_laws. Their PLAIN instances (lib/Reusable/YI5b.v src0_sink_head, ofl_head 0x51950; YI5c.v src0_sink,
   src0_sink_laws) are #[global], and lib/A/AsanTop.v loads them: with AsanTop loaded, a bare sink argument resolved to
   the PLAIN image (a Theorem Labs lane's instance sweep, 2026-10-29). After this file NO sink instance is a hint - neither the
   plain ones nor lib/B's own lib/B/YE2k.v tfib_sink_head (ofl_head 0x5fa0e8) - so a file that loads it must pass the
   ASan+UBSan instances explicitly (@... YE2k.tfib_sink_head, the record YE2k.tfib_K).
   Who Requires it: lib/B/BGates.v, lib/B/ReplyTFIBBParts.v (the B milestone), lib/A/AsanTop.v (the asan-ubsan
   statements), and every lib/B walk file. Require it AFTER any `Import YE2k` (an Import re-activates YE2k's #[export]
   instance). The probes, run with AsanTop loaded, are lib/B/ReplyGuardBCheck.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI16 YI14 YI5b YI5c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YE2k.
#[global] Remove Hints YE2k.tfib_sink_head YI5b.src0_sink_head YI5c.src0_sink YI5c.src0_sink_laws : typeclass_instances.
