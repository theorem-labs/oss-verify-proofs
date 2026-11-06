(* Port-from: origin/cold/c-asan-rt-stateio-n 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Prog/memchr.v.
   Changes (R1Str, 2026-10-29): module path fuzz_state -> fuzz_reply; no address numerals. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Prog Require Import memchr_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require R_memchr.

Theorem memchr_holds : memchr_contract.
Proof. exact R_memchr.memchr_spec. Qed.
