(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: lemmas added for the revision. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsHSTab
  AsStartupPlan AsImages AsPlanImages AsStartup AsanPlanF AsPlanRegen AsStartupHS1.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

(* LPS 727298f3, design 1: the renumbered root plan, once per CONFIG_RSEQ value against that
   value's computed hand-off table; each result shape is computed, then checked hole-only. *)
Definition startup_shape_r0 : shape := Eval vm_compute in
  match root_check 0 HS1_asan_r0 with COk s => s | CErr _ _ _ => SHole 999 end.
Lemma startup_shape_holes_r0 : holes_only startup_shape_r0 = true.
Proof. vm_compute. reflexivity. Qed.
Definition startup_shape_r1 : shape := Eval vm_compute in
  match root_check 1 HS1_asan_r1 with COk s => s | CErr _ _ _ => SHole 999 end.
Lemma startup_shape_holes_r1 : holes_only startup_shape_r1 = true.
Proof. vm_compute. reflexivity. Qed.

From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Lemma startup_cert_r0 :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HS1_asan_r0
    CERT_KC0 CERT_BFUEL CERT_FUEL None (hinit 0) startup_plan_k = COk startup_shape_r0.
Proof. apply FC.check_of_f. cert_refl constr:(COk startup_shape_r0). Qed.
Lemma startup_cert_r1 :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HS1_asan_r1
    CERT_KC0 CERT_BFUEL CERT_FUEL None (hinit 1) startup_plan_k = COk startup_shape_r1.
Proof. apply FC.check_of_f. cert_refl constr:(COk startup_shape_r1). Qed.

Definition startup_shape_k (b : bool) : shape := if b then startup_shape_r1 else startup_shape_r0.
Lemma startup_shape_holes_k : forall b, holes_only (startup_shape_k b) = true.
Proof. intros b. ltac1:(destruct b; [exact startup_shape_holes_r1 | exact startup_shape_holes_r0]). Qed.
Lemma startup_cert_k : forall k : LinuxProcessSemantics.LinuxProcessSem.State.KernelBuild,
  check ASEGS (mk_itab_ranges ASEGS startup_plan_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 (HS1_asan_k (LinuxProcessSemantics.LinuxProcessSem.State.kb_rseq k))
    CERT_KC0 CERT_BFUEL CERT_FUEL None (hinit (rseq_z (LinuxProcessSemantics.LinuxProcessSem.State.kb_rseq k))) startup_plan_k
    = COk (startup_shape_k (LinuxProcessSemantics.LinuxProcessSem.State.kb_rseq k)).
Proof. intros k. ltac1:(destruct (LinuxProcessSemantics.LinuxProcessSem.State.kb_rseq k); [exact startup_cert_r1 | exact startup_cert_r0]). Qed.
