(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue  ItabAsan W0States1 W1St1 W1St2 W1St3 W1St4 W1St5 W1St6 W1St7 W1St8 W1St9 W1St10 W1St11 W1St12 W1St13 W1Plans Main5W1AsanDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma c_616 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]))) (hs_ofS HR_32) 0%nat 400000%nat 5000%nat None (pay_start ST_t9_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)])) t9_arm_nulld2m = COk s_617.
Proof. vm_cast_no_check (eq_refl (COk s_617)). Qed.
Lemma c_632 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]))) (hs_of HT_53) 0%nat 400000%nat 5000%nat None (pay_start ST_c_s9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)])) c_r9 = COk s_633.
Proof. vm_cast_no_check (eq_refl (COk s_633)). Qed.
Lemma c_637 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]))) (hs_of HT_54) 0%nat 400000%nat 5000%nat None (pay_start ST_c_r9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)])) c_s10 = COk s_638.
Proof. vm_cast_no_check (eq_refl (COk s_638)). Qed.
Lemma c_645 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]))) (hs_of HT_55) 0%nat 400000%nat 5000%nat None (pay_start ST_c_s10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)])) c_f10 = COk s_646.
Proof. vm_cast_no_check (eq_refl (COk s_646)). Qed.
Lemma c_656 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]))) (hs_of HT_56) 0%nat 400000%nat 5000%nat None (pay_start ST_c_f10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)])) p10pre = COk s_657.
Proof. vm_cast_no_check (eq_refl (COk s_657)). Qed.
Lemma c_661 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]))) (hs_ofS HR_57) 0%nat 400000%nat 5000%nat None (pay_start ST_t10_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)])) t10_arm_x2 = COk s_662.
Proof. vm_cast_no_check (eq_refl (COk s_662)). Qed.
Lemma c_668 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]))) (hs_ofS HR_32) 0%nat 400000%nat 5000%nat None (pay_start ST_t10_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)])) t10_arm_nulld2m = COk s_669.
Proof. vm_cast_no_check (eq_refl (COk s_669)). Qed.
Lemma c_684 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)]))) HS_none 0%nat 400000%nat 5000%nat None (pay_start ST_c_s10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)])) c_r10 = COk s_685.
Proof. vm_cast_no_check (eq_refl (COk s_685)). Qed.
