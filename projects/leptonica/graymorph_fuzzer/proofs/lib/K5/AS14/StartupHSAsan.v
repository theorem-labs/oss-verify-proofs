(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the hand-off tables computed per CONFIG_RSEQ value by startup_tabs, startup_plan_r and startup_shape, with HS_asan over the run's flag; the recorded HS_asan_0, HS_asan_1000, HS_asan_2000 and HS_asan_3000 removed; the StartupCoGen, StartupPlanAsan, StartupJSAsan, StartupGenAsan0 and StartupGenAsan1 imports). *)
(* THE HAND-OFF TABLE IS COMPUTED, ONE PER CONFIG_RSEQ
   VALUE.  [kb_rseq] is free under [Run.valid_input] ([Run.recorded_kernel], Run.v:4575-4581), so the
   start-up runs from [asan_a_init 0] or [asan_a_init 1].  The recorded [HS_asan_0 .. HS_asan_3000]
   literals, collected over one older initial state, are replaced by the tables [StartupCoGen.gc_go]
   computes from each start state ([StartupGenAsan0], [StartupGenAsan1]); [AsanStartupCert] re-checks
   them, so nothing here is trusted.  [b] is the run's flag. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import AxSymExec3 AsanPlanCore AsanPlan StartupCoGen.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS14 Require Import StartupPlanAsan StartupJSAsan StartupGenAsan0 StartupGenAsan1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition startup_tabs (b : bool) : gc_out := if b then startup_tabs_1 else startup_tabs_0.
(* the hand-off table at the run's flag *)
Definition HS_asan (b : bool) : nat -> option acs := gc_get (go_H (startup_tabs b)).
(* the shipped plan with its join states replaced by the computed ones *)
Definition startup_plan_r (b : bool) : plan := lsub (gc_jget (go_J (startup_tabs b)) js_0) startup_plan.
Definition startup_shape (b : bool) : shape := gc_shape (startup_tabs b).
