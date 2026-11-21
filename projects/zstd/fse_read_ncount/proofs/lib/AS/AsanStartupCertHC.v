(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the certificate is proved at each CONFIG_RSEQ value, for the plan renumbered by the probe-read map (segB's AT_RANDOM split chain rebuilt from probe-read values), against the hand-off states, counters and shape computed in the build). *)
(* The Asan build's start-up certificate for plan C at AsanInit.LIMITH, per CONFIG_RSEQ value and joined;
   its plan, start state, hand-off table and shape are computed in StartupRegenAsan.v (LPS 727298f3).
   Written by gen_startup_regen.py. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages
  AsanInit AsanNodesWJoin AsanCertDefs StartupRegenAsan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.
Lemma startup_certC_h_0 :
check ASEGS ITC ASAN (nxC 0) AsanInit.LIMITH 0 (XNS ASEGS ASAN (nxC 0) AsanInit.LIMITH) XEr XBr (hsC 0) KC0 BFUEL FUEL None (stB 0) (planC 0) = COk (shapeC 0).
Proof. Time (vm_cert_refl constr:(COk (shapeC 0))). Time Qed.
Lemma startup_certC_h_1 :
check ASEGS ITC ASAN (nxC 1) AsanInit.LIMITH 1 (XNS ASEGS ASAN (nxC 1) AsanInit.LIMITH) XEr XBr (hsC 1) KC0 BFUEL FUEL None (stB 1) (planC 1) = COk (shapeC 1).
Proof. Time (vm_cert_refl constr:(COk (shapeC 1))). Time Qed.
Lemma startup_certC_h : forall r, 0 <= r <= 1 ->
check ASEGS ITC ASAN (nxC r) AsanInit.LIMITH r (XNS ASEGS ASAN (nxC r) AsanInit.LIMITH) XEr XBr (hsC r) KC0 BFUEL FUEL None (stB r) (planC r) = COk (shapeC r).
Proof. ltac1:(intros r Hr; assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact startup_certC_h_0 | exact startup_certC_h_1]). Qed.
