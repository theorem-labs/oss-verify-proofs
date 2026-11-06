(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Prog/strlen.v: ported from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/Prog/strlen.v, which equals the A->B relocation (asan-kit elfmap.py + remap.py) of lib/A/Prog/strlen.v at cold/port-fm-int 5d8d8a15571 modulo module paths; module paths for this tree. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require R_strlen.

Theorem strlen_holds : strlen_contract.
Proof. exact R_strlen.strlen_spec. Qed.
