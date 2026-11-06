(* Port-from: origin/cold/c-asan-rt-stateio-n 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Prog/memset.v.
   Changes (PfCalls, 2026-10-29): module path fuzz_state -> fuzz_reply; no address numerals. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Prog Require Import memset_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require R_memset.

Theorem memset_holds : memset_contract.
Proof. exact R_memset.memset_spec. Qed.
