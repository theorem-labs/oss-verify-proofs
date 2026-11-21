(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (one certificate per value of the run's CONFIG_RSEQ flag, of the renumbered plan me_A4_planR, from and against hand-off states computed from the run, and me_A4_cert at the flag's boolean). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AsanPlanCore AsanPlan AsanCertDefs PlanCut MainEntryPiecesAsan StartupRegenAsan MainEntryRegenAsan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
(* [comment removed for export] *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Definition me_A4_shape : shape := SHole 1013.

(* LPS 727298f3: [rz] is [s2_check]'s second argument (AsanCertDefs.v); one lemma per value, from
   and against the states MainEntryRegenAsan.v computes from the run at that value (round C2 of
   this port's probe record read this shape at both values). *)
Lemma me_A4_cert0 : s2_check NX1 0 IT1 (me_A4_tab 0) (HSm_1012 0) me_A4_planR = COk me_A4_shape.
Proof. cert_refl constr:(COk me_A4_shape). Qed.
Lemma me_A4_cert1 : s2_check NX1 1 IT1 (me_A4_tab 1) (HSm_1012 1) me_A4_planR = COk me_A4_shape.
Proof. cert_refl constr:(COk me_A4_shape). Qed.
Lemma me_A4_cert (b : bool) : s2_check NX1 (rseq_z b) IT1 (me_A4_tab (rseq_z b)) (HSm_1012 (rseq_z b)) me_A4_planR = COk me_A4_shape.
Proof. ltac1:(destruct b; [exact me_A4_cert1 | exact me_A4_cert0]). Qed.
