(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB StartupHSMainBoth ItabBoth W0BLib W0BStates1 W0BStates2 W0BPlans ArgleafTmplBoth ArgleafContOAllBoth ContOAll5Both Main5BothDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma c_127 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2)]))) HS_none 0%nat 400000%nat 5000%nat None (pay_start H2002 ([(QLook, 4, 4); (QArgc, 2, 2)])) td30gt = COk s_128.
Proof. vm_cast_no_check (eq_refl (COk s_128)). Qed.
Lemma c_134 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)]))) (hs_ofS HR_8) 0%nat 400000%nat 5000%nat None (pay_start AR0_s (((((((((root_class 5) ++ [(QFlen, QMIN, 65535)]) ++ [(QFlen, 5 + 1, QMAX)]) ++ [(QRoom, (-1) + 1, QMAX)]) ++ [(QRoom, 0 + 1, QMAX)]) ++ [(QRoom, 5888 + 1, QMAX)]) ++ [(QRoom, 7936 + 1, QMAX)]) ++ [(QRoom, 64512 + 1, QMAX)]) ++ [(QRoom, QMIN, 65529)])) p0sec6 = COk s_135.
Proof. vm_cast_no_check (eq_refl (COk s_135)). Qed.
Lemma c_141 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 64513, 65529)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 64513, 65529)]))) HS_none 0%nat 400000%nat 5000%nat None (pay_start HSEC_S ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 64513, 65529)])) tssec = COk s_142.
Proof. vm_cast_no_check (eq_refl (COk s_142)). Qed.
Lemma c_147 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2)]))) HS_none 0%nat 400000%nat 5000%nat None (pay_start HSEC_N ([(QLook, 4, 4); (QArgc, 2, 2)])) tn_sec = COk s_148.
Proof. vm_cast_no_check (eq_refl (COk s_148)). Qed.
Lemma c_158 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2)]))) HS_none 0%nat 400000%nat 5000%nat None (pay_start REP_s ([(QLook, 4, 4); (QArgc, 2, 2)])) rep26 = COk s_159.
Proof. vm_cast_no_check (eq_refl (COk s_159)). Qed.
Lemma c_165 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]))) (hs_ofX HT_9 HR_4) 0%nat 400000%nat 5000%nat None (pay_start HO_s ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)])) w1r = COk s_166.
Proof. vm_cast_no_check (eq_refl (COk s_166)). Qed.
