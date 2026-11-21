(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from CertS1Asan.v: the S1 certificate at CONFIG_RSEQ value 1, with its hand-off and join states computed in the build by one run of the check (PlanRegen.collect_hjf1), in a file of its own so the two values build in parallel. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl PlanRegen.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import AsanPlanImages5 A_Hooks5 PlanS1Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Open Scope Z_scope.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import CertS1AsanD.

(* the hand-off and join states of the run at CONFIG_RSEQ value 1 *)
Definition S1C_1 : list (nat * acs) * list (nat * acs) := Eval vm_compute in collect_hjf1 80 (s1_coll 1).
Definition HS_s1_1 (h : nat) : option acs := match h with 0%nat | 1%nat => hlookup (fst S1C_1) h | _ => None end.

Lemma s1_cert_1 :
  check ASEGS IT1 ASAN5 NX0 AsanInit.LIMIT 1 XN0 XE0 XB0 HS_s1_1 KC0 BFUEL FUEL None (init_acs_of 1 ASAN5) (s1_plan_r 1 (hlookup (snd S1C_1))) = COk s1_shape.
Proof. ltac2:(cert_refl_vm constr:(COk s1_shape)). Qed.
