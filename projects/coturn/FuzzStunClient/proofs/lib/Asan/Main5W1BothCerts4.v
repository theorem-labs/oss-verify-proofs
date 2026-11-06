(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB  ItabBoth W0BStates1 W1BSt1 W1BSt2 W1BSt3 W1BSt4 W1BSt5 W1BSt6 W1BSt7 W1BSt8 W1BSt9 W1BSt10 W1BSt11 W1BSt12 W1BSt13 W1BSt14 W1BPlans Main5W1BothDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma c_362 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]))) (hs_ofS HR_28) 0%nat 400000%nat 5000%nat None (pay_start ST_tb5_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)])) tb5_arm_x2 = COk s_363.
Proof. vm_cast_no_check (eq_refl (COk s_363)). Qed.
Lemma c_369 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]))) (hs_ofS HR_30) 0%nat 400000%nat 5000%nat None (pay_start ST_tb5_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)])) tb5_arm_nulld2mb = COk s_370.
Proof. vm_cast_no_check (eq_refl (COk s_370)). Qed.
Lemma c_376 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]))) HS_none 0%nat 400000%nat 5000%nat None (pay_start T_d2mb ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)])) nl_d2mb = COk s_377.
Proof. vm_cast_no_check (eq_refl (COk s_377)). Qed.
Lemma c_383 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]))) (hs_ofS HR_29) 0%nat 400000%nat 5000%nat None (pay_start T_d2xb5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)])) armxb = COk s_384.
Proof. vm_cast_no_check (eq_refl (COk s_384)). Qed.
Lemma c_390 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]))) HS_none 0%nat 400000%nat 5000%nat None (pay_start T_d2xb5s ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)])) ts_d2xb5s = COk s_391.
Proof. vm_cast_no_check (eq_refl (COk s_391)). Qed.
Lemma c_402 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]))) (hs_of HT_31) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_s5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)])) cb_r5 = COk s_403.
Proof. vm_cast_no_check (eq_refl (COk s_403)). Qed.
Lemma c_407 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]))) (hs_of HT_32) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_r5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)])) cb_s6 = COk s_408.
Proof. vm_cast_no_check (eq_refl (COk s_408)). Qed.
Lemma c_415 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]))) (hs_of HT_33) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_s6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)])) cb_f6 = COk s_416.
Proof. vm_cast_no_check (eq_refl (COk s_416)). Qed.
Lemma c_426 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]))) (hs_of HT_34) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_f6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)])) pb6pre = COk s_427.
Proof. vm_cast_no_check (eq_refl (COk s_427)). Qed.
Lemma c_431 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]))) (hs_ofS HR_35) 0%nat 400000%nat 5000%nat None (pay_start ST_tb6_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)])) tb6_arm_x2 = COk s_432.
Proof. vm_cast_no_check (eq_refl (COk s_432)). Qed.
