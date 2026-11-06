(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB  ItabBoth W0BStates1 W1BSt1 W1BSt2 W1BSt3 W1BSt4 W1BSt5 W1BSt6 W1BSt7 W1BSt8 W1BSt9 W1BSt10 W1BSt11 W1BSt12 W1BSt13 W1BSt14 W1BPlans Main5W1BothDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma c_615 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]))) (hs_of HT_52) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_r9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)])) cb_s10 = COk s_616.
Proof. vm_cast_no_check (eq_refl (COk s_616)). Qed.
Lemma c_623 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]))) (hs_of HT_53) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_s10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)])) cb_f10 = COk s_624.
Proof. vm_cast_no_check (eq_refl (COk s_624)). Qed.
Lemma c_634 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]))) (hs_of HT_54) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_f10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)])) pb10pre = COk s_635.
Proof. vm_cast_no_check (eq_refl (COk s_635)). Qed.
Lemma c_639 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]))) (hs_ofS HR_55) 0%nat 400000%nat 5000%nat None (pay_start ST_tb10_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)])) tb10_arm_x2 = COk s_640.
Proof. vm_cast_no_check (eq_refl (COk s_640)). Qed.
Lemma c_646 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]))) (hs_ofS HR_30) 0%nat 400000%nat 5000%nat None (pay_start ST_tb10_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)])) tb10_arm_nulld2mb = COk s_647.
Proof. vm_cast_no_check (eq_refl (COk s_647)). Qed.
Lemma c_662 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)]))) HS_none 0%nat 400000%nat 5000%nat None (pay_start ST_cb_s10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)])) cb_r10 = COk s_663.
Proof. vm_cast_no_check (eq_refl (COk s_663)). Qed.
