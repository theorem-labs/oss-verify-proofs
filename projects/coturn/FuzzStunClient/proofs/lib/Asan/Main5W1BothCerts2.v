(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB  ItabBoth W0BStates1 W1BSt1 W1BSt2 W1BSt3 W1BSt4 W1BSt5 W1BSt6 W1BSt7 W1BSt8 W1BSt9 W1BSt10 W1BSt11 W1BSt12 W1BSt13 W1BSt14 W1BPlans Main5W1BothDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma c_202 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]))) (hs_ofS HR_12) 0%nat 400000%nat 5000%nat None (pay_start ST_tb2_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)])) tb2_armd5b = COk s_203.
Proof. vm_cast_no_check (eq_refl (COk s_203)). Qed.
Lemma c_209 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]))) HS_none 0%nat 400000%nat 5000%nat None (pay_start ST_tb2_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)])) tb2_arm_n1000 = COk s_210.
Proof. vm_cast_no_check (eq_refl (COk s_210)). Qed.
Lemma c_222 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]))) (hs_of HT_13) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_s2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)])) cb_r2 = COk s_223.
Proof. vm_cast_no_check (eq_refl (COk s_223)). Qed.
Lemma c_227 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]))) (hs_of HT_14) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_r2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)])) cb_s3 = COk s_228.
Proof. vm_cast_no_check (eq_refl (COk s_228)). Qed.
Lemma c_235 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]))) (hs_of HT_15) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_s3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)])) cb_f3 = COk s_236.
Proof. vm_cast_no_check (eq_refl (COk s_236)). Qed.
Lemma c_246 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]))) (hs_of HT_16) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_f3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)])) pb3pre = COk s_247.
Proof. vm_cast_no_check (eq_refl (COk s_247)). Qed.
Lemma c_251 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]))) (hs_ofS HR_17) 0%nat 400000%nat 5000%nat None (pay_start ST_tb3_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)])) tb3_armd5b = COk s_252.
Proof. vm_cast_no_check (eq_refl (COk s_252)). Qed.
Lemma c_258 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]))) HS_none 0%nat 400000%nat 5000%nat None (pay_start ST_tb3_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)])) tb3_arm_n1000 = COk s_259.
Proof. vm_cast_no_check (eq_refl (COk s_259)). Qed.
Lemma c_271 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]))) (hs_of HT_18) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_s3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)])) cb_r3 = COk s_272.
Proof. vm_cast_no_check (eq_refl (COk s_272)). Qed.
Lemma c_276 : check BSEGS IT_both BOTH NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]))) (XEm BSEGS BOTH NX0) (XBm BSEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]))) (hs_of HT_19) 0%nat 400000%nat 5000%nat None (pay_start ST_cb_r3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)])) cb_s4 = COk s_277.
Proof. vm_cast_no_check (eq_refl (COk s_277)). Qed.
