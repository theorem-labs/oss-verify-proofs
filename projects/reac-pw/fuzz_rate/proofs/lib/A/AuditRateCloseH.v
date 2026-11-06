(* reac-pw/fuzz_rate image A: About and Print Assumptions of lib/A/AD2o.v rate_asan_halts_closed, one top in this
   file (the audit of lib/A/AuditRateClose.v, split so that each Print Assumptions is its own compile). Each axiom
   printed must be on toolchain/allowed-axioms.txt. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require AD2o.
Local Open Scope Z_scope.
About AD2o.rate_asan_halts_closed.
Print Assumptions AD2o.rate_asan_halts_closed.
