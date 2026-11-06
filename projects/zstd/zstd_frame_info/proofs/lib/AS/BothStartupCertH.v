(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit AsanNodesWJoin BothStartup StartupPlanBoth StartupHSBoth StartupPlan2Both StartupHS2Both BothCertDefs.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.

Lemma startup_cert_h :
  check BSEGS IT0 BOTH NX0 AsanInit.LIMITH (XNS BSEGS BOTH NX0 AsanInit.LIMITH) XE0 XB0 HS_bothA KC0 BFUEL FUEL None both_init startup_plan_both = COk startup_shape.
Proof. Time (vm_cert_refl constr:(COk startup_shape)). Time Qed.
