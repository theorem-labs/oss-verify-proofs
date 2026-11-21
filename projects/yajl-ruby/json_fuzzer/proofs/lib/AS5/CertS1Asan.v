(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up certificate per CONFIG_RSEQ value: the recorded plan renumbered where it is checked, its join and hand-off states computed in the build; the two values computed and proved in their own files, joined here). *)
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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Export CertS1AsanD CertS1AsanR0 CertS1AsanR1.

(* the per-CONFIG_RSEQ tables, certificates and plan, joined *)
Definition S1C (r : Z) : list (nat * acs) * list (nat * acs) := if Z.eqb r 1 then S1C_1 else S1C_0.
Definition HS_s1 (r : Z) (h : nat) : option acs :=
  match h with 0%nat | 1%nat => hlookup (fst (S1C r)) h | _ => None end.
Definition JS_s1 (r : Z) : nat -> option acs := hlookup (snd (S1C r)).
Definition s1_plan_k (r : Z) : plan := s1_plan_r r (JS_s1 r).

Lemma s1_cert : forall b : bool,
  check ASEGS IT1 ASAN5 NX0 AsanInit.LIMIT (rseq_z b) XN0 XE0 XB0 (HS_s1 (rseq_z b)) KC0 BFUEL FUEL None
        (init_acs_of (rseq_z b) ASAN5) (s1_plan_k (rseq_z b)) = COk s1_shape.
Proof. intros [|]; [exact s1_cert_1 | exact s1_cert_0]. Qed.
