(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the certificate is proved at each CONFIG_RSEQ value, for the plan renumbered by the probe-read map (segB's AT_RANDOM split chain rebuilt from probe-read values), against the hand-off states, counters and shape computed in the build). *)
(* The Both build's start-up certificate for plan 2 at AsanInit.LIMITH, per CONFIG_RSEQ value and joined;
   its plan, start state, hand-off table and shape are computed in StartupRegenBoth.v (LPS 727298f3).
   Written by gen_startup_regen.py. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan BothPlanImages
  AsanInit AsanNodesWJoin BothCertDefs StartupRegenBoth.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.
Lemma startup2_cert_h_0 :
check BSEGS IT2 BOTH (nx2 0) AsanInit.LIMITH 0 (XNS BSEGS BOTH (nx2 0) AsanInit.LIMITH) XEr XBr (hs2 0) KC0 BFUEL FUEL None (stD 0) (plan2 0) = COk (shape2 0).
Proof. Time (vm_cert_refl constr:(COk (shape2 0))). Time Qed.
Lemma startup2_cert_h_1 :
check BSEGS IT2 BOTH (nx2 1) AsanInit.LIMITH 1 (XNS BSEGS BOTH (nx2 1) AsanInit.LIMITH) XEr XBr (hs2 1) KC0 BFUEL FUEL None (stD 1) (plan2 1) = COk (shape2 1).
Proof. Time (vm_cert_refl constr:(COk (shape2 1))). Time Qed.
Lemma startup2_cert_h : forall r, 0 <= r <= 1 ->
check BSEGS IT2 BOTH (nx2 r) AsanInit.LIMITH r (XNS BSEGS BOTH (nx2 r) AsanInit.LIMITH) XEr XBr (hs2 r) KC0 BFUEL FUEL None (stD r) (plan2 r) = COk (shape2 r).
Proof. ltac1:(intros r Hr; assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact startup2_cert_h_0 | exact startup2_cert_h_1]). Qed.
