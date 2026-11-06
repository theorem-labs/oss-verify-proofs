(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB  ItabBoth W0BStates1 W1BSt1 W1BSt2 W1BSt3 W1BSt4 W1BSt5 W1BSt6 W1BSt7 W1BSt8 W1BSt9 W1BSt10 W1BSt11 W1BSt12 W1BSt13 W1BSt14 W1BPlans Main5W1BothDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma c_438 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]))) (hs_ofS HR_30) 0%nat 400000%nat 5000%nat None (pay_start ST_tb6_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)])) tb6_arm_nulld2mb = COk s_439.
Proof. vm_cast_no_check (eq_refl (COk s_439)). Qed.
Lemma c_454 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]))) (hs_of HT_36) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_s6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)])) cb_r6 = COk s_455.
Proof. vm_cast_no_check (eq_refl (COk s_455)). Qed.
Lemma c_459 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]))) (hs_of HT_37) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_r6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)])) cb_s7 = COk s_460.
Proof. vm_cast_no_check (eq_refl (COk s_460)). Qed.
Lemma c_467 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]))) (hs_of HT_38) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_s7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)])) cb_f7 = COk s_468.
Proof. vm_cast_no_check (eq_refl (COk s_468)). Qed.
Lemma c_478 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]))) (hs_of HT_39) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_f7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)])) pb7pre = COk s_479.
Proof. vm_cast_no_check (eq_refl (COk s_479)). Qed.
Lemma c_483 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]))) (hs_ofS HR_40) 0%nat 400000%nat 5000%nat None (pay_start ST_tb7_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)])) tb7_arm_x2 = COk s_484.
Proof. vm_cast_no_check (eq_refl (COk s_484)). Qed.
Lemma c_490 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]))) (hs_ofS HR_30) 0%nat 400000%nat 5000%nat None (pay_start ST_tb7_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)])) tb7_arm_nulld2mb = COk s_491.
Proof. vm_cast_no_check (eq_refl (COk s_491)). Qed.
Lemma c_506 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]))) (hs_of HT_41) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_s7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)])) cb_r7 = COk s_507.
Proof. vm_cast_no_check (eq_refl (COk s_507)). Qed.
Lemma c_511 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]))) (hs_of HT_42) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_r7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)])) cb_s8 = COk s_512.
Proof. vm_cast_no_check (eq_refl (COk s_512)). Qed.
Lemma c_519 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]))) (hs_of HT_43) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_s8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)])) cb_f8 = COk s_520.
Proof. vm_cast_no_check (eq_refl (COk s_520)). Qed.
