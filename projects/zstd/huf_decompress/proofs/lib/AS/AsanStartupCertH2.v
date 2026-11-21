(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the certificate is proved at each CONFIG_RSEQ value, for the plan renumbered by the probe-read map (segB's AT_RANDOM split chain rebuilt from probe-read values), against the hand-off states, counters and shape computed in the build). *)
(* The Asan build's start-up certificate for plan 2 at AsanInit.LIMITH, per CONFIG_RSEQ value and joined;
   its plan, start state, hand-off table and shape are computed in StartupRegenAsan.v (LPS 727298f3).
   Written by gen_startup_regen.py. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages
  AsanInit AsanNodesWJoin AsanCertDefs StartupRegenAsan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.
Lemma startup2_cert_h_0 :
check ASEGS IT2 ASAN (nx2 0) AsanInit.LIMITH 0 (XNS ASEGS ASAN (nx2 0) AsanInit.LIMITH) XEr XBr (hs2 0) KC0 BFUEL FUEL None (stD 0) (plan2 0) = COk (shape2 0).
Proof. (vm_cert_refl constr:(COk (shape2 0))). Time Qed.
Lemma startup2_cert_h_1 :
check ASEGS IT2 ASAN (nx2 1) AsanInit.LIMITH 1 (XNS ASEGS ASAN (nx2 1) AsanInit.LIMITH) XEr XBr (hs2 1) KC0 BFUEL FUEL None (stD 1) (plan2 1) = COk (shape2 1).
Proof. (vm_cert_refl constr:(COk (shape2 1))). Time Qed.
Lemma startup2_cert_h : forall r, 0 <= r <= 1 ->
check ASEGS IT2 ASAN (nx2 r) AsanInit.LIMITH r (XNS ASEGS ASAN (nx2 r) AsanInit.LIMITH) XEr XBr (hs2 r) KC0 BFUEL FUEL None (stD r) (plan2 r) = COk (shape2 r).
Proof. ltac1:(intros r Hr; assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact startup2_cert_h_0 | exact startup2_cert_h_1]). Qed.
