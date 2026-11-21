(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: lemmas added for the revision. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsHSTab
  BsStartupPlan BothImages BothPlanImages BsStartup AsanPlanF AsPlanRegen BsStartupHS1 BsStartupHSC.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

(* LPS 727298f3, design 1: segment 90, renumbered by [G1], once per CONFIG_RSEQ value from that
   value's computed start state against the computed hand-off table of that value; each result shape is
   computed, then checked hole-only. *)
Definition startup_shape_r0 : shape := Eval vm_compute in
  match seg90_run HS1_asan_90_r0 HSC_asan_r0 with COk s => s | CErr _ _ _ => SHole 999 end.
Lemma startup_shape_holes_r0 : holes_only startup_shape_r0 = true.
Proof. vm_compute. reflexivity. Qed.
Definition startup_shape_r1 : shape := Eval vm_compute in
  match seg90_run HS1_asan_90_r1 HSC_asan_r1 with COk s => s | CErr _ _ _ => SHole 999 end.
Lemma startup_shape_holes_r1 : holes_only startup_shape_r1 = true.
Proof. vm_compute. reflexivity. Qed.

From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Lemma startup_cert_r0 :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_seg90_xranges) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSC_asan_r0
    CERT_KC0 CERT_BFUEL CERT_FUEL None HS1_asan_90_r0 startup_plan_seg90_k = COk startup_shape_r0.
Proof. apply FC.check_of_f. cert_refl constr:(COk startup_shape_r0). Qed.
Lemma startup_cert_r1 :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_seg90_xranges) BOTH_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSC_asan_r1
    CERT_KC0 CERT_BFUEL CERT_FUEL None HS1_asan_90_r1 startup_plan_seg90_k = COk startup_shape_r1.
Proof. apply FC.check_of_f. cert_refl constr:(COk startup_shape_r1). Qed.
