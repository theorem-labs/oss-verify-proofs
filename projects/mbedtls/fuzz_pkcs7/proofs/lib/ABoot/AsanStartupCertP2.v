(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (one certificate per value of the run's CONFIG_RSEQ flag, of the renumbered plan su_P2_planR from the computed hand-off state at 1000 against the hand-off states computed from the run, and su_P2_cert at the flag's boolean). *)
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

Definition su_P2_shape : shape := SCase (EVar 6) 10 (SHole 1001) (SCase (EVar 6) 1802 (SHole 1002) (SHole 1003)).

(* LPS 727298f3: [rz] is [s2_check]'s second argument (AsanCertDefs.v); one lemma per value, from
   and against the states StartupRegenAsan.v computes from the run at that value. *)
Lemma su_P2_cert0 : s2_check NX0 0 IT0 (su_P2_tab 0) (HS_1000 0) su_P2_planR = COk su_P2_shape.
Proof. cert_refl constr:(COk su_P2_shape). Qed.
Lemma su_P2_cert1 : s2_check NX0 1 IT0 (su_P2_tab 1) (HS_1000 1) su_P2_planR = COk su_P2_shape.
Proof. cert_refl constr:(COk su_P2_shape). Qed.
Lemma su_P2_cert (b : bool) : s2_check NX0 (rseq_z b) IT0 (su_P2_tab (rseq_z b)) (HS_1000 (rseq_z b)) su_P2_planR = COk su_P2_shape.
Proof. ltac1:(destruct b; [exact su_P2_cert1 | exact su_P2_cert0]). Qed.
