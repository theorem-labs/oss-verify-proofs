(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup StartupPlanAsan StartupHSAsan StartupPlan2Asan StartupHS2Asan AsanCertDefs.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.

Lemma startup_certC :
  check ASEGS ITC ASAN NXC AsanInit.LIMIT (XNS ASEGS ASAN NXC AsanInit.LIMIT) XE0 XB0 HS_asanC KC0 BFUEL FUEL None HS_asanB_11 startup_plan_segB = COk startup_shapeC.
Proof. Time (vm_cert_refl constr:(COk startup_shapeC)). Time Qed.
