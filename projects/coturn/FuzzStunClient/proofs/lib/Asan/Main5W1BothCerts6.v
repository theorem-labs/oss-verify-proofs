(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB  ItabBoth W0BStates1 W1BSt1 W1BSt2 W1BSt3 W1BSt4 W1BSt5 W1BSt6 W1BSt7 W1BSt8 W1BSt9 W1BSt10 W1BSt11 W1BSt12 W1BSt13 W1BSt14 W1BPlans Main5W1BothDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma c_530 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]))) (hs_of HT_44) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_f8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)])) pb8pre = COk s_531.
Proof. vm_cast_no_check (eq_refl (COk s_531)). Qed.
Lemma c_535 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]))) (hs_ofS HR_45) 0%nat 400000%nat 5000%nat None (pay_start ST_tb8_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)])) tb8_arm_x2 = COk s_536.
Proof. vm_cast_no_check (eq_refl (COk s_536)). Qed.
Lemma c_542 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]))) (hs_ofS HR_30) 0%nat 400000%nat 5000%nat None (pay_start ST_tb8_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)])) tb8_arm_nulld2mb = COk s_543.
Proof. vm_cast_no_check (eq_refl (COk s_543)). Qed.
Lemma c_558 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]))) (hs_of HT_46) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_s8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)])) cb_r8 = COk s_559.
Proof. vm_cast_no_check (eq_refl (COk s_559)). Qed.
Lemma c_563 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]))) (hs_of HT_47) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_r8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)])) cb_s9 = COk s_564.
Proof. vm_cast_no_check (eq_refl (COk s_564)). Qed.
Lemma c_571 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]))) (hs_of HT_48) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_s9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)])) cb_f9 = COk s_572.
Proof. vm_cast_no_check (eq_refl (COk s_572)). Qed.
Lemma c_582 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]))) (hs_of HT_49) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_f9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)])) pb9pre = COk s_583.
Proof. vm_cast_no_check (eq_refl (COk s_583)). Qed.
Lemma c_587 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]))) (hs_ofS HR_50) 0%nat 400000%nat 5000%nat None (pay_start ST_tb9_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)])) tb9_arm_x2 = COk s_588.
Proof. vm_cast_no_check (eq_refl (COk s_588)). Qed.
Lemma c_594 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]))) (hs_ofS HR_30) 0%nat 400000%nat 5000%nat None (pay_start ST_tb9_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)])) tb9_arm_nulld2mb = COk s_595.
Proof. vm_cast_no_check (eq_refl (COk s_595)). Qed.
Lemma c_610 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]))) (hs_of HT_51) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_s9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)])) cb_r9 = COk s_611.
Proof. vm_cast_no_check (eq_refl (COk s_611)). Qed.
