(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit AsanNodesWJoin BothStartup StartupPlanBoth StartupHSBoth StartupPlan2Both StartupHS2Both BothCertDefs.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.
Lemma startup_certD_h :
check BSEGS ITD BOTH NXD AsanInit.LIMITH (XNS BSEGS BOTH NXD AsanInit.LIMITH) XE0 XB0 HS_bothD KC0 BFUEL FUEL None HS_bothC_12 startup_plan_both_segC = COk startup_shapeD.
Proof. Time (vm_cert_refl constr:(COk startup_shapeD)). Time Qed.
