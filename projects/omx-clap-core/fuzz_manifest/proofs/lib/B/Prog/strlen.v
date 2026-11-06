(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Prog/strlen.v: ported from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/Prog/strlen.v, which equals the A->B relocation (Theorem Labs tools) of lib/A/Prog/strlen.v at a working branch 5d8d8a15571 modulo module paths; module paths for this tree. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog Require Import strlen_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require R_strlen.

Theorem strlen_holds : strlen_contract.
Proof. exact R_strlen.strlen_spec. Qed.
