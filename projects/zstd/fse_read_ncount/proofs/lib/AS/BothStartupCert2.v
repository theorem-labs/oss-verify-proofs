(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit AsanNodesWJoin BothStartup StartupPlanBoth StartupHSBoth StartupPlan2Both StartupHS2Both BothCertDefs.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2.
Lemma startup2_cert :
check BSEGS IT2 BOTH NXS2 AsanInit.LIMIT (XNS BSEGS BOTH NXS2 AsanInit.LIMIT) XE0 XB0 HS_both2 KC0 BFUEL FUEL None HS_bothD_0 startup2_plan_both = COk startup2_shape.
Proof. Time (vm_cert_refl constr:(COk startup2_shape)). Time Qed.
