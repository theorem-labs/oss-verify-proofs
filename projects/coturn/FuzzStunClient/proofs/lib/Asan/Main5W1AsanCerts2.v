(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue  ItabAsan W0States1 W1St1 W1St2 W1St3 W1St4 W1St5 W1St6 W1St7 W1St8 W1St9 W1St10 W1St11 W1St12 W1St13 W1Plans Main5W1AsanDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma c_207 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]))) (hs_of HT_12) 0%nat 400000%nat 5000%nat None (pay_start ST_c_f2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)])) p2pre = COk s_208.
Proof. vm_cast_no_check (eq_refl (COk s_208)). Qed.
Lemma c_212 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]))) (hs_ofS HR_13) 0%nat 400000%nat 5000%nat None (pay_start ST_t2_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)])) t2_armd5 = COk s_213.
Proof. vm_cast_no_check (eq_refl (COk s_213)). Qed.
Lemma c_219 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]))) (hs_ofS HR_8) 0%nat 400000%nat 5000%nat None (pay_start ST_t2_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)])) t2_arm_nulld0 = COk s_220.
Proof. vm_cast_no_check (eq_refl (COk s_220)). Qed.
Lemma c_235 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]))) (hs_of HT_14) 0%nat 400000%nat 5000%nat None (pay_start ST_c_s2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)])) c_r2 = COk s_236.
Proof. vm_cast_no_check (eq_refl (COk s_236)). Qed.
Lemma c_240 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]))) (hs_of HT_15) 0%nat 400000%nat 5000%nat None (pay_start ST_c_r2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)])) c_s3 = COk s_241.
Proof. vm_cast_no_check (eq_refl (COk s_241)). Qed.
Lemma c_248 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]))) (hs_of HT_16) 0%nat 400000%nat 5000%nat None (pay_start ST_c_s3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)])) c_f3 = COk s_249.
Proof. vm_cast_no_check (eq_refl (COk s_249)). Qed.
Lemma c_259 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]))) (hs_of HT_17) 0%nat 400000%nat 5000%nat None (pay_start ST_c_f3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)])) p3pre = COk s_260.
Proof. vm_cast_no_check (eq_refl (COk s_260)). Qed.
Lemma c_264 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]))) (hs_ofS HR_18) 0%nat 400000%nat 5000%nat None (pay_start ST_t3_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)])) t3_armd5 = COk s_265.
Proof. vm_cast_no_check (eq_refl (COk s_265)). Qed.
Lemma c_271 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]))) HS_none 0%nat 400000%nat 5000%nat None (pay_start ST_t3_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)])) t3_arm_n1000 = COk s_272.
Proof. vm_cast_no_check (eq_refl (COk s_272)). Qed.
Lemma c_284 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]))) (hs_of HT_19) 0%nat 400000%nat 5000%nat None (pay_start ST_c_s3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)])) c_r3 = COk s_285.
Proof. vm_cast_no_check (eq_refl (COk s_285)). Qed.
