(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AsanPlanCore AsanPlan AsanCertDefs PlanCut StartupPlanAsan StartupHSAsan StartupHScutAsan StartupPiecesAsan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanStartupCertP3B () : Init.string Init.list := ["OSSVerify.KrLib.ABoot.AsanPlan.AP.SAlt2"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.SHole"].

(* [comment removed for export] *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Definition su_P3B_shape : shape := ltac2:(CDefT.buildp (gd_tbl_AsanStartupCertP3B ()) "(0.(0.(1.#0.)(0.(1.#0.)(0.(1.#0.)(1.#0.))))(0.(0.(1.#0.)(1.#0.))(0.(0.(1.#0.)(1.#0.))(0.(1.#0.)(1.#0.)))))")
(* [comment removed for export] *).

Lemma su_P3B_cert : s2_check NX0 IT0 HS_asan HS_s1c_1002 su_P3B_plan = COk su_P3B_shape.
Proof. cert_refl constr:(COk su_P3B_shape). Qed.
