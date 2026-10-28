(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AsanPlanCore AsanPlan. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PlanCut. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import StartupHSAsan MainEntryPlanAsan MainEntryHSAsan MainEntryHScutAsan MainEntryPiecesAsan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MainEntryCertAsanR0 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.SCase"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.EAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.EMd"; "LinuxProcessSemantics.Riscv.Instr.M_MUL"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.ELit"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.EVar"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.SHole"].

(* [comment removed for export] *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Definition me_R0_shape : shape := ltac2:(CDefT.buildp (gd_tbl_MainEntryCertAsanR0 ()) "(0.(1.$2.(1.$2.(3.$4.(5.+10.)(6.#6.))(3.$4.(5.-1000.)(6.#167.)))(5.+?5?.))+?;>.(7.#3>8.)(7.#3>9.))")
(* [comment removed for export] *).

Lemma me_R0_cert : s2_check NX1 IT1 me_R0_tab HS_asan_0 me_R0_plan = COk me_R0_shape.
Proof. cert_refl constr:(COk me_R0_shape). Qed.
