(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue  ItabAsan W0States1 W1St1 W1St2 W1St3 W1St4 W1St5 W1St6 W1St7 W1St8 W1St9 W1St10 W1St11 W1St12 W1St13 W1Plans Main5W1AsanDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma c_368 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]))) (hs_of HT_28) 0%nat 400000%nat 5000%nat None (pay_start ST_c_s5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)])) c_f5 = COk s_369.
Proof. vm_cast_no_check (eq_refl (COk s_369)). Qed.
Lemma c_379 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]))) (hs_of HT_29) 0%nat 400000%nat 5000%nat None (pay_start ST_c_f5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)])) p5pre = COk s_380.
Proof. vm_cast_no_check (eq_refl (COk s_380)). Qed.
Lemma c_384 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]))) (hs_ofS HR_30) 0%nat 400000%nat 5000%nat None (pay_start ST_t5_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)])) t5_arm_x2 = COk s_385.
Proof. vm_cast_no_check (eq_refl (COk s_385)). Qed.
Lemma c_391 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]))) (hs_ofS HR_32) 0%nat 400000%nat 5000%nat None (pay_start ST_t5_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)])) t5_arm_nulld2m = COk s_392.
Proof. vm_cast_no_check (eq_refl (COk s_392)). Qed.
Lemma c_398 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]))) HS_none 0%nat 400000%nat 5000%nat None (pay_start T_d2m ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)])) nl_d2m = COk s_399.
Proof. vm_cast_no_check (eq_refl (COk s_399)). Qed.
Lemma c_405 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]))) (hs_ofS HR_31) 0%nat 400000%nat 5000%nat None (pay_start T_d2x ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)])) armxs = COk s_406.
Proof. vm_cast_no_check (eq_refl (COk s_406)). Qed.
Lemma c_412 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]))) HS_none 0%nat 400000%nat 5000%nat None (pay_start T_d2xs ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)])) ts_d2xs = COk s_413.
Proof. vm_cast_no_check (eq_refl (COk s_413)). Qed.
Lemma c_424 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]))) (hs_of HT_33) 0%nat 400000%nat 5000%nat None (pay_start ST_c_s5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)])) c_r5 = COk s_425.
Proof. vm_cast_no_check (eq_refl (COk s_425)). Qed.
Lemma c_429 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]))) (hs_of HT_34) 0%nat 400000%nat 5000%nat None (pay_start ST_c_r5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)])) c_s6 = COk s_430.
Proof. vm_cast_no_check (eq_refl (COk s_430)). Qed.
Lemma c_437 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]))) (hs_of HT_35) 0%nat 400000%nat 5000%nat None (pay_start ST_c_s6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)])) c_f6 = COk s_438.
Proof. vm_cast_no_check (eq_refl (COk s_438)). Qed.
