(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the certificate is proved at each CONFIG_RSEQ value, for the plan renumbered by the probe-read map (segB's AT_RANDOM split chain rebuilt from probe-read values), against the hand-off states, counters and shape computed in the build). *)
(* The Both build's start-up certificate for plan C at AsanInit.LIMIT, per CONFIG_RSEQ value and joined;
   its plan, start state, hand-off table and shape are computed in StartupRegenBoth.v (LPS 727298f3).
   Written by gen_startup_regen.py. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan BothPlanImages
  AsanInit AsanNodesWJoin BothCertDefs StartupRegenBoth.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.
Lemma startup_certC_0 :
check ASEGS ITC BOTH (nxC 0) AsanInit.LIMIT 0 (XNS ASEGS BOTH (nxC 0) AsanInit.LIMIT) XEr XBr (hsC 0) KC0 BFUEL FUEL None (stB 0) (planC 0) = COk (shapeC 0).
Proof. (vm_cert_refl constr:(COk (shapeC 0))). Time Qed.
Lemma startup_certC_1 :
check ASEGS ITC BOTH (nxC 1) AsanInit.LIMIT 1 (XNS ASEGS BOTH (nxC 1) AsanInit.LIMIT) XEr XBr (hsC 1) KC0 BFUEL FUEL None (stB 1) (planC 1) = COk (shapeC 1).
Proof. (vm_cert_refl constr:(COk (shapeC 1))). Time Qed.
Lemma startup_certC : forall r, 0 <= r <= 1 ->
check ASEGS ITC BOTH (nxC r) AsanInit.LIMIT r (XNS ASEGS BOTH (nxC r) AsanInit.LIMIT) XEr XBr (hsC r) KC0 BFUEL FUEL None (stB r) (planC r) = COk (shapeC r).
Proof. ltac1:(intros r Hr; assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact startup_certC_0 | exact startup_certC_1]). Qed.
