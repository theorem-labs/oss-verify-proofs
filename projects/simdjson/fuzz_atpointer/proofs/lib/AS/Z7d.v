(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the certificates check the renumbered plan with the join and hand-off states computed in the build, one per CONFIG_RSEQ value). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z78 Z2z Z2y Z33 Z3h Z31 Z1s Z3d Z10h PlanRegen Z10s Z10sr.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From Ltac2 Require Import Ltac2 Constr Std Control.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
Definition IT0 : itab := mk_itab_ranges ASEGS startup_plan_ranges.
Lemma IT0_ok : itab_sound ASEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.

Definition startup_shape : shape := (SHole 0).

(* TWO CLOSED CERTIFICATES, ONE PER [b : bool]; image B's twin of AS/Z3f.v.

   [asan_b_init] takes the rseq index r because the revision's auxv vector is
   rseq-dependent: AT_NULL sits at pair [26 + 2 * r] (Z2z.v:3530) and the whole
   vector is [AUXSZ r = 432 + 32 * r] bytes
   (75d69e00:theories/Common/AsanPlanCore.v:3192).  So the two launches this
   image can take lay out 432 bytes with AT_NULL at 416, and 464 with AT_NULL at
   448 -- 416 = 16 * 26 and 448 = 16 * 28 are the terminator's own offsets, and
   each total is that plus the terminator pair's 16 bytes.

   A single r-PARAMETRIC certificate is NOT available here.  [cert_refl] casts
   an [eq_refl] through [vm_compute]; under a binder for r the [check] call has
   no closed argument to reduce, so the cast cannot decide it.  The model states
   the same rule for its own certificates: "a certificate is checked at one
   literal value" (75d69e00:theories/Common/AsanPlan.v:35).

   Two closed certificates are NOT a kernel pin and NOT an rseq pin.  Neither
   value is fixed by anything here: [startup_cert] discharges the free boolean
   by cases and BOTH branches exist, so a caller at
   [kb_rseq (in_kernel inp)] gets its certificate whichever way the flag falls.
   [valid_input]'s last conjunct is [in_kernel inp = recorded_kernel (in_kernel inp)]
   (75d69e00:theories/LinuxProcessSem/Run.v:4596), and [recorded_kernel]
   PRESERVES [kb_rseq] (ibid.:4575-4577) -- so the flag stays free and a premise
   fixing it would be one no caller could discharge. *)
Lemma startup_cert_r0 :
  check ASEGS IT0 ASAN_B NX0 Z1s.LIMIT 0 XN0 XE0 XB0 (HS_both_r 0) KC0 BFUEL FUEL None (asan_b_init 0)
        (startup_plan_rB 0) = COk startup_shape.
Proof. cert_refl constr:(COk startup_shape). Qed.

Lemma startup_cert_r1 :
  check ASEGS IT0 ASAN_B NX0 Z1s.LIMIT 1 XN0 XE0 XB0 (HS_both_r 1) KC0 BFUEL FUEL None (asan_b_init 1)
        (startup_plan_rB 1) = COk startup_shape.
Proof. cert_refl constr:(COk startup_shape). Qed.

Lemma startup_cert : forall b : bool,
  check ASEGS IT0 ASAN_B NX0 Z1s.LIMIT (rseq_z b) XN0 XE0 XB0 (HS_both_r (rseq_z b)) KC0 BFUEL FUEL None
        (asan_b_init (rseq_z b)) (startup_plan_rB (rseq_z b)) = COk startup_shape.
Proof. ltac1:(intros [|]; [exact startup_cert_r1 | exact startup_cert_r0]). Qed.
