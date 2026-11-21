(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (one certificate per value of the run's CONFIG_RSEQ flag, of the renumbered plan me_R0_planR, from and against hand-off states computed from the run, and me_R0_cert at the flag's boolean; the shape written out in plain text, with the variable the run now numbers 365 where the recorded shape named 359). *)
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

Definition me_R0_shape : shape := SCase (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16) (EVar 6)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 365))) (ELit 3935))
    4030 (SHole 1000) (SHole 1001).

(* LPS 727298f3: [rz] is [s2_check]'s second argument (AsanCertDefs.v); one lemma per value, from
   and against the states MainEntryRegenAsan.v computes from the run at that value (round C2 of
   this port's probe record read this shape at both values). *)
Lemma me_R0_cert0 : s2_check NX1 0 IT1 (me_R0_tab 0) (HS_0 0) me_R0_planR = COk me_R0_shape.
Proof. cert_refl constr:(COk me_R0_shape). Qed.
Lemma me_R0_cert1 : s2_check NX1 1 IT1 (me_R0_tab 1) (HS_0 1) me_R0_planR = COk me_R0_shape.
Proof. cert_refl constr:(COk me_R0_shape). Qed.
Lemma me_R0_cert (b : bool) : s2_check NX1 (rseq_z b) IT1 (me_R0_tab (rseq_z b)) (HS_0 (rseq_z b)) me_R0_planR = COk me_R0_shape.
Proof. ltac1:(destruct b; [exact me_R0_cert1 | exact me_R0_cert0]). Qed.
