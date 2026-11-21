(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the certificate is proved at each CONFIG_RSEQ value, for the plan renumbered by the probe-read map (segB's AT_RANDOM split chain rebuilt from probe-read values), against the hand-off states, counters and shape computed in the build). *)
(* The Asan build's start-up certificate for plan D at AsanInit.LIMITH, per CONFIG_RSEQ value and joined;
   its plan, start state, hand-off table and shape are computed in StartupRegenAsan.v (LPS 727298f3).
   Written by gen_startup_regen.py. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages
  AsanInit AsanNodesWJoin AsanCertDefs StartupRegenAsan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.
Lemma startup_certD_h_0 :
check ASEGS ITD ASAN (nxD 0) AsanInit.LIMITH 0 (XNS ASEGS ASAN (nxD 0) AsanInit.LIMITH) XEr XBr (hsD 0) KC0 BFUEL FUEL None (stC 0) (planD 0) = COk (shapeD 0).
Proof. Time (vm_cert_refl constr:(COk (shapeD 0))). Time Qed.
Lemma startup_certD_h_1 :
check ASEGS ITD ASAN (nxD 1) AsanInit.LIMITH 1 (XNS ASEGS ASAN (nxD 1) AsanInit.LIMITH) XEr XBr (hsD 1) KC0 BFUEL FUEL None (stC 1) (planD 1) = COk (shapeD 1).
Proof. Time (vm_cert_refl constr:(COk (shapeD 1))). Time Qed.
Lemma startup_certD_h : forall r, 0 <= r <= 1 ->
check ASEGS ITD ASAN (nxD r) AsanInit.LIMITH r (XNS ASEGS ASAN (nxD r) AsanInit.LIMITH) XEr XBr (hsD r) KC0 BFUEL FUEL None (stC r) (planD r) = COk (shapeD r).
Proof. ltac1:(intros r Hr; assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact startup_certD_h_0 | exact startup_certD_h_1]). Qed.
