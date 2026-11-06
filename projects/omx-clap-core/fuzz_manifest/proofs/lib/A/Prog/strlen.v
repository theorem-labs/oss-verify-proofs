(* Ported by a Theorem Labs lane from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Prog/strlen.v, unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog Require Import strlen_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require R_strlen.

Theorem strlen_holds : strlen_contract.
Proof. exact R_strlen.strlen_spec. Qed.
