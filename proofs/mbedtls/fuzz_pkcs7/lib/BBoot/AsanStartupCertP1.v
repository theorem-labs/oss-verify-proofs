(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AsanPlanCore AsanPlan. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PlanCut. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import StartupPlanAsan StartupHSAsan StartupHScutAsan StartupPiecesAsan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
(* [comment removed for export] *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Definition su_P1_shape : shape := SAlt2 SNil (SAlt2 SNil (SAlt2 SNil (SHole 1000))).

Lemma su_P1_cert : s1_check IT0 su_P1_tab su_P1_plan = COk su_P1_shape.
Proof. cert_refl constr:(COk su_P1_shape). Qed.
