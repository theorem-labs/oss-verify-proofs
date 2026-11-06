(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit AsanNodesWJoin BothStartup StartupPlanBoth StartupHSBoth BothStartupCert.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITB : itab := mk_itab_ranges BSEGS startup_plan_both_ranges_A.
Lemma ITB_ok : itab_sound BSEGS ITB.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* [comment removed for export] *)
Definition NXB : nat := 207%nat.
Lemma NXB_ge : (NX0 <= NXB)%nat. Proof. unfold NX0, NXB. lia. Qed.
Definition startup_shapeB : shape := SHole 11.
From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma startup_certB :
  check BSEGS ITB BOTH NXB AsanInit.LIMIT (XNS BSEGS BOTH NXB AsanInit.LIMIT) XE0 XB0 HS_bothB KC0 BFUEL FUEL None HS_bothA_10 startup_plan_both_segA = COk startup_shapeB.
Proof. Time (vm_cert_refl constr:(COk startup_shapeB)). Time Qed.
