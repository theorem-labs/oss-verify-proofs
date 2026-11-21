(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the certificate is proved at each CONFIG_RSEQ value, for the plan renumbered by the probe-read map (segB's AT_RANDOM split chain rebuilt from probe-read values), against the hand-off states, counters and shape computed in the build). *)
(* The Asan build's start-up certificate for plan B at AsanInit.LIMIT, per CONFIG_RSEQ value and joined;
   its plan, start state, hand-off table and shape are computed in StartupRegenAsan.v (LPS 727298f3).
   Written by gen_startup_regen.py. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages
  AsanInit AsanNodesWJoin AsanCertDefs StartupRegenAsan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.
Lemma startup_certB_0 :
check BSEGS ITB ASAN (nxB 0) AsanInit.LIMIT 0 (XNS BSEGS ASAN (nxB 0) AsanInit.LIMIT) XEr XBr (hsB 0) KC0 BFUEL FUEL None (stA 0) (planB 0) = COk (shapeB 0).
Proof. Time (vm_cert_refl constr:(COk (shapeB 0))). Time Qed.
Lemma startup_certB_1 :
check BSEGS ITB ASAN (nxB 1) AsanInit.LIMIT 1 (XNS BSEGS ASAN (nxB 1) AsanInit.LIMIT) XEr XBr (hsB 1) KC0 BFUEL FUEL None (stA 1) (planB 1) = COk (shapeB 1).
Proof. Time (vm_cert_refl constr:(COk (shapeB 1))). Time Qed.
Lemma startup_certB : forall r, 0 <= r <= 1 ->
check BSEGS ITB ASAN (nxB r) AsanInit.LIMIT r (XNS BSEGS ASAN (nxB r) AsanInit.LIMIT) XEr XBr (hsB r) KC0 BFUEL FUEL None (stA r) (planB r) = COk (shapeB r).
Proof. ltac1:(intros r Hr; assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact startup_certB_0 | exact startup_certB_1]). Qed.
