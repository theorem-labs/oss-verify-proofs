From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestEnd.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require ManifestEnd.

Definition omx_clap_core_fuzz_manifest_plain_halts :=
  OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog.ManifestEnd.plain_halts_holds.
Definition omx_clap_core_fuzz_manifest_ubsan_halts :=
  OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog.ManifestEnd.ubsan_halts_holds.
