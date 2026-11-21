(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/AU/AuditHeadampCloseU.v (itself
   proofs/libreac/fuzz_knock/lib/AU/AuditKnockCloseU.v as ported for reac-pw), split:
   the About / Print Assumptions pair of image B's agreement top, whose Print Assumptions walks the whole frame, in its
   own file so that no audit file compiles for more than 20 minutes. Each axiom printed must be on
   toolchain/allowed-axioms.txt. *)
(* Modified by Theorem Labs, 2026-11: internal commit ids in comments replaced by public commits or removed. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require YD2o.
About YD2o.headamp_asan_ubsan_agrees_closed.
Print Assumptions YD2o.headamp_asan_ubsan_agrees_closed.
