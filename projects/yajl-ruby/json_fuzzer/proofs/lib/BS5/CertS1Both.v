(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up certificate per CONFIG_RSEQ value: the recorded plan checked with its join and hand-off states computed in the build; the two values computed and proved in their own files, the tables joined in CertS1BothT.v and the certificates joined here). *)
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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Export CertS1BothD CertS1BothT CertS1BothR0 CertS1BothR1.

(* the per-CONFIG_RSEQ certificates, joined (the tables are CertS1BothT.v's) *)
Lemma s1_cert : forall b : bool,
  check BSEGS IT1 BOTH5 NX0 AsanInit.LIMIT (rseq_z b) XN0 XE0 XB0 (HS_s1 (rseq_z b)) KC0 BFUEL FUEL None
        (init_acs_of (rseq_z b) BOTH5) (s1_plan_k (rseq_z b)) = COk s1_shape.
Proof. intros [|]; [exact s1_cert_1 | exact s1_cert_0]. Qed.
