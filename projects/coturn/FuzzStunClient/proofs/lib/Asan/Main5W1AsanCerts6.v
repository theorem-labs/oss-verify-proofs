(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue  ItabAsan W0States1 W1St1 W1St2 W1St3 W1St4 W1St5 W1St6 W1St7 W1St8 W1St9 W1St10 W1St11 W1St12 W1St13 W1Plans Main5W1AsanDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma c_533 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]))) (hs_of HT_44) 0%nat 400000%nat 5000%nat None (pay_start ST_c_r7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)])) c_s8 = COk s_534.
Proof. vm_cast_no_check (eq_refl (COk s_534)). Qed.
Lemma c_541 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]))) (hs_of HT_45) 0%nat 400000%nat 5000%nat None (pay_start ST_c_s8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)])) c_f8 = COk s_542.
Proof. vm_cast_no_check (eq_refl (COk s_542)). Qed.
Lemma c_552 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]))) (hs_of HT_46) 0%nat 400000%nat 5000%nat None (pay_start ST_c_f8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)])) p8pre = COk s_553.
Proof. vm_cast_no_check (eq_refl (COk s_553)). Qed.
Lemma c_557 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]))) (hs_ofS HR_47) 0%nat 400000%nat 5000%nat None (pay_start ST_t8_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)])) t8_arm_x2 = COk s_558.
Proof. vm_cast_no_check (eq_refl (COk s_558)). Qed.
Lemma c_564 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]))) (hs_ofS HR_32) 0%nat 400000%nat 5000%nat None (pay_start ST_t8_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)])) t8_arm_nulld2m = COk s_565.
Proof. vm_cast_no_check (eq_refl (COk s_565)). Qed.
Lemma c_580 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]))) (hs_of HT_48) 0%nat 400000%nat 5000%nat None (pay_start ST_c_s8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)])) c_r8 = COk s_581.
Proof. vm_cast_no_check (eq_refl (COk s_581)). Qed.
Lemma c_585 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]))) (hs_of HT_49) 0%nat 400000%nat 5000%nat None (pay_start ST_c_r8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)])) c_s9 = COk s_586.
Proof. vm_cast_no_check (eq_refl (COk s_586)). Qed.
Lemma c_593 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]))) (hs_of HT_50) 0%nat 400000%nat 5000%nat None (pay_start ST_c_s9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)])) c_f9 = COk s_594.
Proof. vm_cast_no_check (eq_refl (COk s_594)). Qed.
Lemma c_604 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]))) (hs_of HT_51) 0%nat 400000%nat 5000%nat None (pay_start ST_c_f9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)])) p9pre = COk s_605.
Proof. vm_cast_no_check (eq_refl (COk s_605)). Qed.
Lemma c_609 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]))) (hs_ofS HR_52) 0%nat 400000%nat 5000%nat None (pay_start ST_t9_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)])) t9_arm_x2 = COk s_610.
Proof. vm_cast_no_check (eq_refl (COk s_610)). Qed.
