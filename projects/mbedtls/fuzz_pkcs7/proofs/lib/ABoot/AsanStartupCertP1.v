(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (one certificate per value of the run's CONFIG_RSEQ flag, of the renumbered plan su_P1_planR against the hand-off state computed from the run, and su_P1_cert at the flag's boolean). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AsanPlanCore AsanPlan AsanCertDefs PlanCut StartupPlanAsan StartupPiecesAsan StartupRegenAsan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
(* [comment removed for export] *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Definition su_P1_shape : shape := SAlt2 SNil (SAlt2 SNil (SAlt2 SNil (SHole 1000))).

(* LPS 727298f3: [rz] is [s1_check]'s first argument (AsanCertDefs.v); one lemma per value, against
   the hand-off table StartupRegenAsan.v computes from the run at that value. *)
Lemma su_P1_cert0 : s1_check 0 IT0 (su_P1_tab 0) su_P1_planR = COk su_P1_shape.
Proof. cert_refl constr:(COk su_P1_shape). Qed.
Lemma su_P1_cert1 : s1_check 1 IT0 (su_P1_tab 1) su_P1_planR = COk su_P1_shape.
Proof. cert_refl constr:(COk su_P1_shape). Qed.
Lemma su_P1_cert (b : bool) : s1_check (rseq_z b) IT0 (su_P1_tab (rseq_z b)) su_P1_planR = COk su_P1_shape.
Proof. ltac1:(destruct b; [exact su_P1_cert1 | exact su_P1_cert0]). Qed.
