(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup StartupPlanAsan StartupHSAsan StartupPlan2Asan StartupHS2Asan AsanCertDefs.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.

Lemma startup2_cert :
  check ASEGS IT2 ASAN NXS2 AsanInit.LIMIT (XNS ASEGS ASAN NXS2 AsanInit.LIMIT) XE0 XB0 HS_asan2 KC0 BFUEL FUEL None HS_asanD_0 startup2_plan = COk startup2_shape.
Proof. Time (vm_cert_refl constr:(COk startup2_shape)). Time Qed.
