(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (one certificate per value of the run's CONFIG_RSEQ flag, of the renumbered plan su_P3A_planR from the computed hand-off state at 1001 against the hand-off state at 0 computed from the run, and su_P3A_cert at the flag's boolean). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AsanPlanCore AsanPlan AsanCertDefs PlanCut StartupPlanAsan StartupPiecesAsan StartupRegenAsan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanStartupCertP3A () : Init.string Init.list := ["OSSVerify.KrLib.ABoot.AsanPlan.AP.SAlt2"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.SHole"].

(* [comment removed for export] *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Definition su_P3A_shape : shape := ltac2:(CDefT.buildp (gd_tbl_AsanStartupCertP3A ()) "(0.(0.(1.#0.)(0.(1.#0.)(0.(1.#0.)(1.#0.))))(0.(0.(1.#0.)(1.#0.))(0.(0.(1.#0.)(1.#0.))(0.(1.#0.)(1.#0.)))))")
(* [comment removed for export] *).

(* LPS 727298f3: [rz] is [s2_check]'s second argument (AsanCertDefs.v); one lemma per value, from
   and against the states StartupRegenAsan.v computes from the run at that value. *)
Lemma su_P3A_cert0 : s2_check NX0 0 IT0 (su_P3_tab 0) (HS_1001 0) su_P3A_planR = COk su_P3A_shape.
Proof. cert_refl constr:(COk su_P3A_shape). Qed.
Lemma su_P3A_cert1 : s2_check NX0 1 IT0 (su_P3_tab 1) (HS_1001 1) su_P3A_planR = COk su_P3A_shape.
Proof. cert_refl constr:(COk su_P3A_shape). Qed.
Lemma su_P3A_cert (b : bool) : s2_check NX0 (rseq_z b) IT0 (su_P3_tab (rseq_z b)) (HS_1001 (rseq_z b)) su_P3A_planR = COk su_P3A_shape.
Proof. ltac1:(destruct b; [exact su_P3A_cert1 | exact su_P3A_cert0]). Qed.
