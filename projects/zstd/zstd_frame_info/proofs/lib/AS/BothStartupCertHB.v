(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit AsanNodesWJoin BothStartup StartupPlanBoth StartupHSBoth StartupPlan2Both StartupHS2Both BothCertDefs.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.

Lemma startup_certB_h :
  check BSEGS ITB BOTH NXB AsanInit.LIMITH (XNS BSEGS BOTH NXB AsanInit.LIMITH) XE0 XB0 HS_bothB KC0 BFUEL FUEL None HS_bothA_10 startup_plan_both_segA = COk startup_shapeB.
Proof. Time (vm_cert_refl constr:(COk startup_shapeB)). Time Qed.
