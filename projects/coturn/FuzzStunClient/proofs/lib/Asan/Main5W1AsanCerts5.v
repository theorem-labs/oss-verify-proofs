(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue  ItabAsan W0States1 W1St1 W1St2 W1St3 W1St4 W1St5 W1St6 W1St7 W1St8 W1St9 W1St10 W1St11 W1St12 W1St13 W1Plans Main5W1AsanDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma c_448 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]))) (hs_of HT_36) 0%nat 400000%nat 5000%nat None (pay_start ST_c_f6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)])) p6pre = COk s_449.
Proof. vm_cast_no_check (eq_refl (COk s_449)). Qed.
Lemma c_453 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]))) (hs_ofS HR_37) 0%nat 400000%nat 5000%nat None (pay_start ST_t6_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)])) t6_arm_x2 = COk s_454.
Proof. vm_cast_no_check (eq_refl (COk s_454)). Qed.
Lemma c_460 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]))) (hs_ofS HR_32) 0%nat 400000%nat 5000%nat None (pay_start ST_t6_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)])) t6_arm_nulld2m = COk s_461.
Proof. vm_cast_no_check (eq_refl (COk s_461)). Qed.
Lemma c_476 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]))) (hs_of HT_38) 0%nat 400000%nat 5000%nat None (pay_start ST_c_s6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)])) c_r6 = COk s_477.
Proof. vm_cast_no_check (eq_refl (COk s_477)). Qed.
Lemma c_481 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]))) (hs_of HT_39) 0%nat 400000%nat 5000%nat None (pay_start ST_c_r6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)])) c_s7 = COk s_482.
Proof. vm_cast_no_check (eq_refl (COk s_482)). Qed.
Lemma c_489 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]))) (hs_of HT_40) 0%nat 400000%nat 5000%nat None (pay_start ST_c_s7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)])) c_f7 = COk s_490.
Proof. vm_cast_no_check (eq_refl (COk s_490)). Qed.
Lemma c_500 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]))) (hs_of HT_41) 0%nat 400000%nat 5000%nat None (pay_start ST_c_f7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)])) p7pre = COk s_501.
Proof. vm_cast_no_check (eq_refl (COk s_501)). Qed.
Lemma c_505 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]))) (hs_ofS HR_42) 0%nat 400000%nat 5000%nat None (pay_start ST_t7_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)])) t7_arm_x2 = COk s_506.
Proof. vm_cast_no_check (eq_refl (COk s_506)). Qed.
Lemma c_512 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]))) (hs_ofS HR_32) 0%nat 400000%nat 5000%nat None (pay_start ST_t7_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)])) t7_arm_nulld2m = COk s_513.
Proof. vm_cast_no_check (eq_refl (COk s_513)). Qed.
Lemma c_528 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]))) (hs_of HT_43) 0%nat 400000%nat 5000%nat None (pay_start ST_c_s7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)])) c_r7 = COk s_529.
Proof. vm_cast_no_check (eq_refl (COk s_529)). Qed.
