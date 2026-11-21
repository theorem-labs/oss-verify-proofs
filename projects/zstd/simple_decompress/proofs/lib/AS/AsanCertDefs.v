(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (made from this unit's AsanStartupCert, AsanStartupCertB, AsanStartupCertC, AsanStartupCertD and AsanStartupCert2: their fuels, instruction tables and vm_cert_refl, now shared by the certificates regenerated per CONFIG_RSEQ value). *)
(* The Asan build's start-up certificates' shared definitions (as zstd/fse_read_ncount's AsanCertDefs.v): the
   fuels, the per-plan instruction tables and the vm-cast tactic.  Before LPS 727298f3 each certificate file
   defined its own; the certificates written from StartupRegenAsan.v import them from here. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin StartupPlanAsan StartupPlan2Asan.
Unset Lia Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
Definition IT0 : itab := mk_itab_ranges BSEGS startup_plan_both_ranges_0.
Lemma IT0_ok : itab_sound BSEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition ITB : itab := mk_itab_ranges BSEGS startup_plan_both_ranges_A.
Lemma ITB_ok : itab_sound BSEGS ITB.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition ITC : itab := mk_itab_ranges BSEGS startup_plan_both_ranges_B.
Lemma ITC_ok : itab_sound BSEGS ITC.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition ITD : itab := mk_itab_ranges BSEGS startup_plan_both_ranges_C.
Lemma ITD_ok : itab_sound BSEGS ITD.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition IT2 : itab := mk_itab_ranges BSEGS startup2_plan_both_ranges.
Lemma IT2_ok : itab_sound BSEGS IT2.
Proof. apply APS.mk_itab_ranges_sound. Qed.
From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
