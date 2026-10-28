(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Image MpiCoreAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepEcp EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_ecp_defs.
Import ListNotations.
Open Scope Z_scope.

Lemma U_curve_statics : forall m id, mem_inv usegs m -> 1 <= id <= 13 -> curve_statics usegs (U_CA id) U_ONE id m.
Proof.
  intros m id MI Hid.
  assert (C : id = 1 \/ id = 2 \/ id = 3 \/ id = 4 \/ id = 5 \/ id = 6 \/ id = 7 \/ id = 8 \/ id = 9 \/ id = 10 \/ id = 11 \/ id = 12 \/ id = 13) by lia.
  Ltac one MI := apply static_limbs_image; [exact MI| vm_compute; reflexivity| reflexivity| reflexivity| cbn; lia| cbn; lia].
  destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]];
    unfold curve_statics, U_ONE; cbn [U_CA ca_P ca_A ca_B ca_GX ca_GY ca_N cP cA cB cGX cGY cN has_A is_sw];
    (split; [one MI|]); (split; [intros HA; first [discriminate HA| one MI]|]); (split; [intros HS; first [discriminate HS| split; [one MI| split; one MI]]|]); (split; one MI).
Qed.
