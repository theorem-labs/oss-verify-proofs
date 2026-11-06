(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit AsanNodesWJoin BothStartup StartupPlanBoth StartupHSBoth StartupPlan2Both StartupHS2Both BothCertDefs.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.
Lemma startup_certC_h :
check BSEGS ITC BOTH NXC AsanInit.LIMITH (XNS BSEGS BOTH NXC AsanInit.LIMITH) XE0 XB0 HS_bothC KC0 BFUEL FUEL None HS_bothB_11 startup_plan_both_segB = COk startup_shapeC.
Proof. Time (vm_cert_refl constr:(COk startup_shapeC)). Time Qed.
