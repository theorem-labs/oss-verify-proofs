(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the startup shapes and their bounds removed (startup_shape, startup_shapeB, startup_shapeC, startup_shapeD, startup2_shape, NXB, NXC, NXD, NXS2 and their _ge lemmas), now computed in StartupRegenAsan; 5 recorded proofs replaced by written proofs (IT0_ok, ITB_ok, ITC_ok, ITD_ok, IT2_ok); no longer imports AsanStartup, StartupHSAsan and StartupHS2Asan; the port of zstd/zstd_frame_info's same file). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin StartupPlanAsan StartupPlan2Asan.
Unset Lia Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
(* [comment removed for export] *)
Definition IT0 : itab := mk_itab_ranges ASEGS startup_plan_ranges_0.
Lemma IT0_ok : itab_sound ASEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition ITB : itab := mk_itab_ranges ASEGS startup_plan_ranges_A.
Lemma ITB_ok : itab_sound ASEGS ITB.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ITC : itab := mk_itab_ranges ASEGS startup_plan_ranges_B.
Lemma ITC_ok : itab_sound ASEGS ITC.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ITD : itab := mk_itab_ranges ASEGS startup_plan_ranges_C.
Lemma ITD_ok : itab_sound ASEGS ITD.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition IT2 : itab := mk_itab_ranges ASEGS startup2_plan_ranges.
Lemma IT2_ok : itab_sound ASEGS IT2.
Proof. apply APS.mk_itab_ranges_sound. Qed.

From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
