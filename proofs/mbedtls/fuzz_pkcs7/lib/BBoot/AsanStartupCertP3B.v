(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AsanPlanCore AsanPlan. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PlanCut. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import StartupPlanAsan StartupHSAsan StartupHScutAsan StartupPiecesAsan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanStartupCertP3B () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.SAlt2"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.SHole"].

(* [comment removed for export] *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Definition su_P3B_shape : shape := ltac2:(CDefT.buildp (gd_tbl_AsanStartupCertP3B ()) "(0.(0.(1.#0.)(0.(1.#0.)(0.(1.#0.)(1.#0.))))(0.(0.(1.#0.)(1.#0.))(0.(0.(1.#0.)(1.#0.))(0.(1.#0.)(1.#0.)))))")
(* [comment removed for export] *).

Lemma su_P3B_cert : s2_check NX0 IT0 HS_asan HS_s1c_1002 su_P3B_plan = COk su_P3B_shape.
Proof. cert_refl constr:(COk su_P3B_shape). Qed.
