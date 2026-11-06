(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/AuditHeadampClose.v (itself
   proofs/libreac/fuzz_knock/lib/A/AuditKnockClose.v at origin/ossv/recipes 6ebe35ba632 as ported for reac-pw), split: the
   About / Print Assumptions pair of image A's agreement top, whose Print Assumptions walks the whole relocated frame
   (this file takes 582 s on the build VM with the closed top), in its own file so that no audit file compiles for more than 20
   minutes. Each axiom printed must be on toolchain/allowed-axioms.txt. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require AD2o.
About AD2o.headamp_asan_agrees_closed.
Print Assumptions AD2o.headamp_asan_agrees_closed.
