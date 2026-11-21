(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the startup shapes and their bounds removed (startup_shape, startup_shapeB, startup_shapeC, startup_shapeD, startup2_shape, NXB, NXC, NXD, NXS2 and their _ge lemmas); no longer imports BothStartup, StartupHSBoth and StartupHS2Both). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit AsanNodesWJoin StartupPlanBoth StartupPlan2Both.
Unset Lia Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
(* [comment removed for export] *)
Definition IT0 : itab := mk_itab_ranges BSEGS startup_plan_both_ranges_0.
Lemma IT0_ok : itab_sound BSEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition ITB : itab := mk_itab_ranges BSEGS startup_plan_both_ranges_A.
Lemma ITB_ok : itab_sound BSEGS ITB.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ITC : itab := mk_itab_ranges BSEGS startup_plan_both_ranges_B.
Lemma ITC_ok : itab_sound BSEGS ITC.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ITD : itab := mk_itab_ranges BSEGS startup_plan_both_ranges_C.
Lemma ITD_ok : itab_sound BSEGS ITD.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition IT2 : itab := mk_itab_ranges BSEGS startup2_plan_both_ranges.
Lemma IT2_ok : itab_sound BSEGS IT2.
Proof. apply APS.mk_itab_ranges_sound. Qed.

From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
