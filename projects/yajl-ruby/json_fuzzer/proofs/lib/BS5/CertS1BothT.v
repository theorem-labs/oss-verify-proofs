(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from CertS1Both.v as in the LPS 727298f3 update: the per-CONFIG_RSEQ hand-off and join tables computed in the build, joined (S1C, HS_s1, JS_s1, s1_plan_k), without the certificate, so the S2 collections (HS2Both*.v) do not wait for it. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl PlanRegen.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import A_Hooks5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import AsanPlanImagesB PlanS1Both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Export CertS1BothD CertS1BothC0 CertS1BothC1.

(* the per-CONFIG_RSEQ tables and plan, joined *)
Definition S1C (r : Z) : list (nat * acs) * list (nat * acs) := if Z.eqb r 1 then S1C_1 else S1C_0.
Definition HS_s1 (r : Z) (h : nat) : option acs :=
  match h with 0%nat | 1%nat => hlookup (fst (S1C r)) h | _ => None end.
Definition JS_s1 (r : Z) : nat -> option acs := hlookup (snd (S1C r)).
Definition s1_plan_k (r : Z) : plan := s1_plan_r r (JS_s1 r).
