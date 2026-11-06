(* Modified by Theorem Labs, 2026-10: copied from plugin-hostd/fuzz_reply (a working branch 86b50358d34) to libreac/fuzz_boxreg's asan-ubsan tree lib/B: module paths changed, no other change. *)
(* Ported from: a working branch 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Prog/memset.v.
   Changes (a Theorem Labs lane, 2026-10-29): module path fuzz_state -> fuzz_reply; no address numerals. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import memset_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require R_memset.

Theorem memset_holds : memset_contract.
Proof. exact R_memset.memset_spec. Qed.
