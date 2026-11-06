(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB StartupHSMainBoth ItabBoth ArgleafPlansBoth ArgleafTmplBoth ArgleafContOAllBoth ContOAll5Both ArgR234PlansBoth ArgR3BothDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma c_4 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ((root_class 3) ++ [(QL1, QMIN, 0)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ((root_class 3) ++ [(QL1, QMIN, 0)]))) (hs_ofS HR_1) 0%nat 400000%nat 5000%nat None (pay_start (HSA HS_mainB 0%nat) ((root_class 3) ++ [(QL1, QMIN, 0)])) pfx_o3b3 = COk s_5.
Proof. vm_cast_no_check (eq_refl (COk s_5)). Qed.
Lemma c_14 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of (((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, QMIN, 62)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of (((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, QMIN, 62)]))) (hs_ofS HR_1) 0%nat 400000%nat 5000%nat None (pay_start (HSA HS_mainB 0%nat) (((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, QMIN, 62)])) pfx_o3b3 = COk s_15.
Proof. vm_cast_no_check (eq_refl (COk s_15)). Qed.
Lemma c_22 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, QMIN, 63)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, QMIN, 63)]))) (hs_ofS HR_1) 0%nat 400000%nat 5000%nat None (pay_start (HSA HS_mainB 0%nat) ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, QMIN, 63)])) pfx_o3b3 = COk s_23.
Proof. vm_cast_no_check (eq_refl (COk s_23)). Qed.
Lemma c_29 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, 63 + 1, QMAX)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, 63 + 1, QMAX)]))) (hs_ofS HR_1) 0%nat 400000%nat 5000%nat None (pay_start (HSA HS_mainB 0%nat) ((((root_class 3) ++ [(QL1, 0 + 1, QMAX)]) ++ [(QL1, 62 + 1, QMAX)]) ++ [(QL1, 63 + 1, QMAX)])) pfx_o3b3 = COk s_30.
Proof. vm_cast_no_check (eq_refl (COk s_30)). Qed.
