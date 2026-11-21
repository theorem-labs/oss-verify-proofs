(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from CertS1Both.v: the S1 certificate at CONFIG_RSEQ value 0, checked against the hand-off and join states CertS1BothC0.v computes in the build (the join states filtered by the run record's fixed rule, CertS1BothD.jkeep), in a file of its own so the two values build in parallel and the states' consumers do not wait for it. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl PlanRegen.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import A_Hooks5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import AsanPlanImagesB PlanS1Both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Open Scope Z_scope.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import CertS1BothD CertS1BothC0.

Lemma s1_cert_0 :
  check BSEGS IT1 BOTH5 NX0 AsanInit.LIMIT 0 XN0 XE0 XB0 HS_s1_0 KC0 BFUEL FUEL None (init_acs_of 0 BOTH5) (s1_plan_r 0 (hlookup (snd S1C_0))) = COk s1_shape.
Proof. ltac2:(cert_refl_vm constr:(COk s1_shape)). Qed.
