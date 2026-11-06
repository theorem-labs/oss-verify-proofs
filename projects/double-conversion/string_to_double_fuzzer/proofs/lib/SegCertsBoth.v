(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs StartupHSBoth KindHSBoth MainHSBoth SegJ1Both SegBoth MainItabBoth.
From Ltac2 Require Import Ltac2 Constr Std Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Section TTS.
Variable TT : nat -> option (acs * plan * shape).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition HT_j1 : list (nat * (nat * acs)) := [(0%nat, (0%nat, HSA HS_kind_both 0)); (1%nat, (0%nat, HSA HS_kind_both 1))].
Definition s_j1 : shape := SCase (EVar 5) 524277 (SAlt2 (SHole 1) (SAlt2 (SHole 1) (SAlt2 (SHole 1) (SHole 1)))) (SAlt2 (SHole 1) (SAlt2 (SHole 1) (SAlt2 (SHole 1) (SHole 1)))).
Lemma j1_ok : pre0_check HS_both KCm BFUELm FUELm BITm TT 0%nat HT_j1 seg_j1_both = COk s_j1.
Proof. ltac2:(cert_refl constr:(COk s_j1)). Qed.
Lemma j1_holes : all_holes s_j1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma j1_lv : forallb (fun e : nat * (nat * acs) => Nat.eqb (fst (snd e)) 0) HT_j1 = true. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition HT_m : list (nat * (nat * acs)) := [(0%nat, (0%nat, HSA HS_main_both 0))].
Definition s_m : shape := SHole 0.
Lemma m_ok : pre0_check HS_kind_both KCm BFUELm FUELm BITm TT 0%nat HT_m seg_u_both = COk s_m.
Proof. ltac2:(cert_refl constr:(COk s_m)). Qed.
Lemma m_holes : all_holes s_m = true. Proof. vm_compute. reflexivity. Qed.
Lemma m_lv : forallb (fun e : nat * (nat * acs) => Nat.eqb (fst (snd e)) 0) HT_m = true. Proof. reflexivity. Qed.
End TTS.
