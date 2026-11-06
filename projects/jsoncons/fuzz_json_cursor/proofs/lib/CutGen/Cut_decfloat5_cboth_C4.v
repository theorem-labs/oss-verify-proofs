(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm9PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib Pm9CutKitD DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeapA CutVFT.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import Cut_decfloat5_cboth_T Cut_decfloat5_cboth_R0p0 Cut_decfloat5_cboth_R0p1 Cut_decfloat5_cboth_R0p2 Cut_decfloat5_cboth_R0p3 Cut_decfloat5_cboth_R1p0 Cut_decfloat5_cboth_R1p1 Cut_decfloat5_cboth_R2 Cut_decfloat5_cboth_R3 Cut_decfloat5_cboth_R4 Cut_decfloat5_cboth_R5 Cut_decfloat5_cboth_R6 Cut_decfloat5_cboth_R7 Cut_decfloat5_cboth_R8 Cut_decfloat5_cboth_R9 Cut_decfloat5_cboth_R10 Cut_decfloat5_cboth_R11 Cut_decfloat5_cboth_D.
Lemma lsub240 : CXD.lems_chk LEMS (CAD.po_ops o240) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert240 : as0_cutd_cert ITR BF cp240 (CAD.po_ops o240) (CAD.po_ops2 o240) (CAD.po_plan o240) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub241 : CXD.lems_chk LEMS (CAD.po_ops o241) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert241 : as0_cutd_cert ITR BF cp241 (CAD.po_ops o241) (CAD.po_ops2 o241) (CAD.po_plan o241) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub242 : CXD.lems_chk LEMS (CAD.po_ops o242) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert242 : as0_cutd_cert ITR BF cp242 (CAD.po_ops o242) (CAD.po_ops2 o242) (CAD.po_plan o242) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub243 : CXD.lems_chk LEMS (CAD.po_ops o243) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert243 : as0_cutd_cert ITR BF cp243 (CAD.po_ops o243) (CAD.po_ops2 o243) (CAD.po_plan o243) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub244 : CXD.lems_chk LEMS (CAD.po_ops o244) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert244 : as0_cutd_cert ITR BF cp244 (CAD.po_ops o244) (CAD.po_ops2 o244) (CAD.po_plan o244) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub245 : CXD.lems_chk LEMS (CAD.po_ops o245) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert245 : as0_cutd_cert ITR BF cp245 (CAD.po_ops o245) (CAD.po_ops2 o245) (CAD.po_plan o245) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub246 : CXD.lems_chk LEMS (CAD.po_ops o246) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert246 : as0_cutd_cert ITR BF cp246 (CAD.po_ops o246) (CAD.po_ops2 o246) (CAD.po_plan o246) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub247 : CXD.lems_chk LEMS (CAD.po_ops o247) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert247 : as0_cutd_cert ITR BF cp247 (CAD.po_ops o247) (CAD.po_ops2 o247) (CAD.po_plan o247) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub248 : CXD.lems_chk LEMS (CAD.po_ops o248) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert248 : as0_cutd_cert ITR BF cp248 (CAD.po_ops o248) (CAD.po_ops2 o248) (CAD.po_plan o248) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub249 : CXD.lems_chk LEMS (CAD.po_ops o249) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert249 : as0_cutd_cert ITR BF cp249 (CAD.po_ops o249) (CAD.po_ops2 o249) (CAD.po_plan o249) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub250 : CXD.lems_chk LEMS (CAD.po_ops o250) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert250 : as0_cutd_cert ITR BF cp250 (CAD.po_ops o250) (CAD.po_ops2 o250) (CAD.po_plan o250) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub251 : CXD.lems_chk LEMS (CAD.po_ops o251) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert251 : as0_cutd_cert ITR BF cp251 (CAD.po_ops o251) (CAD.po_ops2 o251) (CAD.po_plan o251) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub252 : CXD.lems_chk LEMS (CAD.po_ops o252) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert252 : as0_cutd_cert ITR BF cp252 (CAD.po_ops o252) (CAD.po_ops2 o252) (CAD.po_plan o252) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub253 : CXD.lems_chk LEMS (CAD.po_ops o253) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert253 : as0_cutd_cert ITR BF cp253 (CAD.po_ops o253) (CAD.po_ops2 o253) (CAD.po_plan o253) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub254 : CXD.lems_chk LEMS (CAD.po_ops o254) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert254 : as0_cutd_cert ITR BF cp254 (CAD.po_ops o254) (CAD.po_ops2 o254) (CAD.po_plan o254) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub255 : CXD.lems_chk LEMS (CAD.po_ops o255) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert255 : as0_cutd_cert ITR BF cp255 (CAD.po_ops o255) (CAD.po_ops2 o255) (CAD.po_plan o255) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub256 : CXD.lems_chk LEMS (CAD.po_ops o256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert256 : as0_cutd_cert ITR BF cp256 (CAD.po_ops o256) (CAD.po_ops2 o256) (CAD.po_plan o256) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub257 : CXD.lems_chk LEMS (CAD.po_ops o257) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert257 : as0_cutd_cert ITR BF cp257 (CAD.po_ops o257) (CAD.po_ops2 o257) (CAD.po_plan o257) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub258 : CXD.lems_chk LEMS (CAD.po_ops o258) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert258 : as0_cutd_cert ITR BF cp258 (CAD.po_ops o258) (CAD.po_ops2 o258) (CAD.po_plan o258) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub259 : CXD.lems_chk LEMS (CAD.po_ops o259) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert259 : as0_cutd_cert ITR BF cp259 (CAD.po_ops o259) (CAD.po_ops2 o259) (CAD.po_plan o259) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub260 : CXD.lems_chk LEMS (CAD.po_ops o260) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert260 : as0_cutd_cert ITR BF cp260 (CAD.po_ops o260) (CAD.po_ops2 o260) (CAD.po_plan o260) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub261 : CXD.lems_chk LEMS (CAD.po_ops o261) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert261 : as0_cutd_cert ITR BF cp261 (CAD.po_ops o261) (CAD.po_ops2 o261) (CAD.po_plan o261) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub262 : CXD.lems_chk LEMS (CAD.po_ops o262) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert262 : as0_cutd_cert ITR BF cp262 (CAD.po_ops o262) (CAD.po_ops2 o262) (CAD.po_plan o262) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub263 : CXD.lems_chk LEMS (CAD.po_ops o263) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert263 : as0_cutd_cert ITR BF cp263 (CAD.po_ops o263) (CAD.po_ops2 o263) (CAD.po_plan o263) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub264 : CXD.lems_chk LEMS (CAD.po_ops o264) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert264 : as0_cutd_cert ITR BF cp264 (CAD.po_ops o264) (CAD.po_ops2 o264) (CAD.po_plan o264) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub265 : CXD.lems_chk LEMS (CAD.po_ops o265) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert265 : as0_cutd_cert ITR BF cp265 (CAD.po_ops o265) (CAD.po_ops2 o265) (CAD.po_plan o265) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub266 : CXD.lems_chk LEMS (CAD.po_ops o266) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert266 : as0_cutd_cert ITR BF cp266 (CAD.po_ops o266) (CAD.po_ops2 o266) (CAD.po_plan o266) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub267 : CXD.lems_chk LEMS (CAD.po_ops o267) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert267 : as0_cutd_cert ITR BF cp267 (CAD.po_ops o267) (CAD.po_ops2 o267) (CAD.po_plan o267) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub268 : CXD.lems_chk LEMS (CAD.po_ops o268) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert268 : as0_cutd_cert ITR BF cp268 (CAD.po_ops o268) (CAD.po_ops2 o268) (CAD.po_plan o268) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub269 : CXD.lems_chk LEMS (CAD.po_ops o269) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert269 : as0_cutd_cert ITR BF cp269 (CAD.po_ops o269) (CAD.po_ops2 o269) (CAD.po_plan o269) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub270 : CXD.lems_chk LEMS (CAD.po_ops o270) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert270 : as0_cutd_cert ITR BF cp270 (CAD.po_ops o270) (CAD.po_ops2 o270) (CAD.po_plan o270) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub271 : CXD.lems_chk LEMS (CAD.po_ops o271) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert271 : as0_cutd_cert ITR BF cp271 (CAD.po_ops o271) (CAD.po_ops2 o271) (CAD.po_plan o271) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub272 : CXD.lems_chk LEMS (CAD.po_ops o272) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert272 : as0_cutd_cert ITR BF cp272 (CAD.po_ops o272) (CAD.po_ops2 o272) (CAD.po_plan o272) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub273 : CXD.lems_chk LEMS (CAD.po_ops o273) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert273 : as0_cutd_cert ITR BF cp273 (CAD.po_ops o273) (CAD.po_ops2 o273) (CAD.po_plan o273) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub274 : CXD.lems_chk LEMS (CAD.po_ops o274) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert274 : as0_cutd_cert ITR BF cp274 (CAD.po_ops o274) (CAD.po_ops2 o274) (CAD.po_plan o274) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub275 : CXD.lems_chk LEMS (CAD.po_ops o275) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert275 : as0_cutd_cert ITR BF cp275 (CAD.po_ops o275) (CAD.po_ops2 o275) (CAD.po_plan o275) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub276 : CXD.lems_chk LEMS (CAD.po_ops o276) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert276 : as0_cutd_cert ITR BF cp276 (CAD.po_ops o276) (CAD.po_ops2 o276) (CAD.po_plan o276) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub277 : CXD.lems_chk LEMS (CAD.po_ops o277) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert277 : as0_cutd_cert ITR BF cp277 (CAD.po_ops o277) (CAD.po_ops2 o277) (CAD.po_plan o277) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub278 : CXD.lems_chk LEMS (CAD.po_ops o278) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert278 : as0_cutd_cert ITR BF cp278 (CAD.po_ops o278) (CAD.po_ops2 o278) (CAD.po_plan o278) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub279 : CXD.lems_chk LEMS (CAD.po_ops o279) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert279 : as0_cutd_cert ITR BF cp279 (CAD.po_ops o279) (CAD.po_ops2 o279) (CAD.po_plan o279) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub280 : CXD.lems_chk LEMS (CAD.po_ops o280) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert280 : as0_cutd_cert ITR BF cp280 (CAD.po_ops o280) (CAD.po_ops2 o280) (CAD.po_plan o280) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub281 : CXD.lems_chk LEMS (CAD.po_ops o281) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert281 : as0_cutd_cert ITR BF cp281 (CAD.po_ops o281) (CAD.po_ops2 o281) (CAD.po_plan o281) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub282 : CXD.lems_chk LEMS (CAD.po_ops o282) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert282 : as0_cutd_cert ITR BF cp282 (CAD.po_ops o282) (CAD.po_ops2 o282) (CAD.po_plan o282) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub283 : CXD.lems_chk LEMS (CAD.po_ops o283) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert283 : as0_cutd_cert ITR BF cp283 (CAD.po_ops o283) (CAD.po_ops2 o283) (CAD.po_plan o283) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub284 : CXD.lems_chk LEMS (CAD.po_ops o284) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert284 : as0_cutd_cert ITR BF cp284 (CAD.po_ops o284) (CAD.po_ops2 o284) (CAD.po_plan o284) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub285 : CXD.lems_chk LEMS (CAD.po_ops o285) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert285 : as0_cutd_cert ITR BF cp285 (CAD.po_ops o285) (CAD.po_ops2 o285) (CAD.po_plan o285) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub286 : CXD.lems_chk LEMS (CAD.po_ops o286) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert286 : as0_cutd_cert ITR BF cp286 (CAD.po_ops o286) (CAD.po_ops2 o286) (CAD.po_plan o286) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub287 : CXD.lems_chk LEMS (CAD.po_ops o287) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert287 : as0_cutd_cert ITR BF cp287 (CAD.po_ops o287) (CAD.po_ops2 o287) (CAD.po_plan o287) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub288 : CXD.lems_chk LEMS (CAD.po_ops o288) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert288 : as0_cutd_cert ITR BF cp288 (CAD.po_ops o288) (CAD.po_ops2 o288) (CAD.po_plan o288) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub289 : CXD.lems_chk LEMS (CAD.po_ops o289) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert289 : as0_cutd_cert ITR BF cp289 (CAD.po_ops o289) (CAD.po_ops2 o289) (CAD.po_plan o289) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub290 : CXD.lems_chk LEMS (CAD.po_ops o290) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert290 : as0_cutd_cert ITR BF cp290 (CAD.po_ops o290) (CAD.po_ops2 o290) (CAD.po_plan o290) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub291 : CXD.lems_chk LEMS (CAD.po_ops o291) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert291 : as0_cutd_cert ITR BF cp291 (CAD.po_ops o291) (CAD.po_ops2 o291) (CAD.po_plan o291) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub292 : CXD.lems_chk LEMS (CAD.po_ops o292) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert292 : as0_cutd_cert ITR BF cp292 (CAD.po_ops o292) (CAD.po_ops2 o292) (CAD.po_plan o292) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub293 : CXD.lems_chk LEMS (CAD.po_ops o293) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert293 : as0_cutd_cert ITR BF cp293 (CAD.po_ops o293) (CAD.po_ops2 o293) (CAD.po_plan o293) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub294 : CXD.lems_chk LEMS (CAD.po_ops o294) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert294 : as0_cutd_cert ITR BF cp294 (CAD.po_ops o294) (CAD.po_ops2 o294) (CAD.po_plan o294) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub295 : CXD.lems_chk LEMS (CAD.po_ops o295) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert295 : as0_cutd_cert ITR BF cp295 (CAD.po_ops o295) (CAD.po_ops2 o295) (CAD.po_plan o295) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub296 : CXD.lems_chk LEMS (CAD.po_ops o296) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert296 : as0_cutd_cert ITR BF cp296 (CAD.po_ops o296) (CAD.po_ops2 o296) (CAD.po_plan o296) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub297 : CXD.lems_chk LEMS (CAD.po_ops o297) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert297 : as0_cutd_cert ITR BF cp297 (CAD.po_ops o297) (CAD.po_ops2 o297) (CAD.po_plan o297) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub298 : CXD.lems_chk LEMS (CAD.po_ops o298) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert298 : as0_cutd_cert ITR BF cp298 (CAD.po_ops o298) (CAD.po_ops2 o298) (CAD.po_plan o298) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub299 : CXD.lems_chk LEMS (CAD.po_ops o299) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert299 : as0_cutd_cert ITR BF cp299 (CAD.po_ops o299) (CAD.po_ops2 o299) (CAD.po_plan o299) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
