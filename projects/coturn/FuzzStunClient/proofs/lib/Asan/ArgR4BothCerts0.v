(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB StartupHSMainBoth ItabBoth ArgleafPlansBoth ArgleafTmplBoth ArgleafContOAllBoth ContOAll5Both ArgR234PlansBoth ArgR4RepBoth ArgR4BothDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma c_3 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of (root_class 4))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of (root_class 4))) (hs_ofS HR_1) 0%nat 400000%nat 5000%nat None (pay_start (HSA HS_mainB 0%nat) (root_class 4)) argdb1otr = COk s_4.
Proof. vm_cast_no_check (eq_refl (COk s_4)). Qed.
Lemma c_10 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ((root_class 4)))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ((root_class 4)))) HS_none 0%nat 400000%nat 5000%nat None (pay_start REP4b_s ((root_class 4))) argdb1o_tospin1 = COk s_11.
Proof. vm_cast_no_check (eq_refl (COk s_11)). Qed.
