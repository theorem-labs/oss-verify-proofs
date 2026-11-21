(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: lemmas added for the revision. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsHSTab
  AsStartupPlan AsImages AsPlanImages AsStartup AsanPlanF AsPlanRegen AsStartupHS1 AsStartupHSC AsStartupHSA AsStartupHSF AsStartupItab.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

(* LPS 727298f3, design 1: segment 100, renumbered by [G1], once per CONFIG_RSEQ value from that
   value's computed start state against the computed hand-off table (the main-entry table is one for both values); each result shape is
   computed, then checked hole-only. *)
Definition startup_shape_r0 : shape := Eval vm_compute in
  match seg100_run HSA_asan_100_r0 HSF_asan with COk s => s | CErr _ _ _ => SHole 999 end.
Lemma startup_shape_holes_r0 : holes_only startup_shape_r0 = true.
Proof. vm_compute. reflexivity. Qed.
Definition startup_shape_r1 : shape := Eval vm_compute in
  match seg100_run HSA_asan_100_r1 HSF_asan with COk s => s | CErr _ _ _ => SHole 999 end.
Lemma startup_shape_holes_r1 : holes_only startup_shape_r1 = true.
Proof. vm_compute. reflexivity. Qed.

From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Lemma startup_cert_r0 :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_seg100_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSF_asan
    CERT_KC0 CERT_BFUEL CERT_FUEL None HSA_asan_100_r0 startup_plan_seg100_k = COk startup_shape_r0.
Proof. ltac1:(rewrite <- ARM_ITAB_eq). apply FC.check_of_f. cert_refl constr:(COk startup_shape_r0). Qed.
Lemma startup_cert_r1 :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_seg100_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HSF_asan
    CERT_KC0 CERT_BFUEL CERT_FUEL None HSA_asan_100_r1 startup_plan_seg100_k = COk startup_shape_r1.
Proof. ltac1:(rewrite <- ARM_ITAB_eq). apply FC.check_of_f. cert_refl constr:(COk startup_shape_r1). Qed.
