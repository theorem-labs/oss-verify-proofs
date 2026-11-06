(* Port-from: origin/cold/c-asan-rt-stateio-n 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Prog/strlen.v.
   Changes (R1Str, 2026-10-29): module path fuzz_state -> fuzz_reply; no address numerals. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Prog Require Import strlen_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require R_strlen.

Theorem strlen_holds : strlen_contract.
Proof. exact R_strlen.strlen_spec. Qed.
