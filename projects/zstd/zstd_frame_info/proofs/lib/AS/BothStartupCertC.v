(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the certificate is proved at each CONFIG_RSEQ value, for the plan renumbered by the probe-read map (segB's AT_RANDOM split chain rebuilt from probe-read values), against the hand-off states, counters and shape computed in the build). *)
(* The Both build's start-up certificate for plan C at AsanInit.LIMIT, per CONFIG_RSEQ value and joined;
   its plan, start state, hand-off table and shape are computed in StartupRegenBoth.v (LPS 727298f3).
   Written by gen_startup_regen.py. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan BothPlanImages
  AsanInit AsanNodesWJoin BothCertDefs StartupRegenBoth.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.
Lemma startup_certC_0 :
check BSEGS ITC BOTH (nxC 0) AsanInit.LIMIT 0 (XNS BSEGS BOTH (nxC 0) AsanInit.LIMIT) XEr XBr (hsC 0) KC0 BFUEL FUEL None (stB 0) (planC 0) = COk (shapeC 0).
Proof. Time (vm_cert_refl constr:(COk (shapeC 0))). Time Qed.
Lemma startup_certC_1 :
check BSEGS ITC BOTH (nxC 1) AsanInit.LIMIT 1 (XNS BSEGS BOTH (nxC 1) AsanInit.LIMIT) XEr XBr (hsC 1) KC0 BFUEL FUEL None (stB 1) (planC 1) = COk (shapeC 1).
Proof. Time (vm_cert_refl constr:(COk (shapeC 1))). Time Qed.
Lemma startup_certC : forall r, 0 <= r <= 1 ->
check BSEGS ITC BOTH (nxC r) AsanInit.LIMIT r (XNS BSEGS BOTH (nxC r) AsanInit.LIMIT) XEr XBr (hsC r) KC0 BFUEL FUEL None (stB r) (planC r) = COk (shapeC r).
Proof. ltac1:(intros r Hr; assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact startup_certC_0 | exact startup_certC_1]). Qed.
