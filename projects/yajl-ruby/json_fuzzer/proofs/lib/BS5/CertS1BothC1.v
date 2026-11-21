(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from CertS1BothR1.v as in the LPS 727298f3 update (CertS1Both.v's S1 certificate at CONFIG_RSEQ value 1): its hand-off and join states, computed in the build by one run of the check (PlanRegen.collect_hjf1, the join states filtered by the run record's fixed rule, CertS1BothD.jkeep), in a file of their own so their consumers do not wait for the certificate. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl PlanRegen.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import A_Hooks5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import AsanPlanImagesB PlanS1Both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import CertS1BothD.

(* the hand-off and join states of the run at CONFIG_RSEQ value 1 *)
Definition S1C_1 : list (nat * acs) * list (nat * acs) := Eval vm_compute in collect_hjf1 80 (s1_coll 1).
Definition HS_s1_1 (h : nat) : option acs := match h with 0%nat | 1%nat => hlookup (fst S1C_1) h | _ => None end.
