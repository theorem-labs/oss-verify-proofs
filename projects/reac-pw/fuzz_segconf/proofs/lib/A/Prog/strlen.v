(* Ported by RtStr from proofs/omx-clap-core/fuzz_manifest/lib/A/Prog/strlen.v, unchanged. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require R_strlen.

Theorem strlen_holds : strlen_contract.
Proof. exact R_strlen.strlen_spec. Qed.
