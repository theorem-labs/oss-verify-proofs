(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanNodesWJoin AsanStartup StartupPlanAsan StartupHSAsan AsanStartupCert.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition ITC : itab := mk_itab_ranges BSEGS startup_plan_both_ranges_B.
Lemma ITC_ok : itab_sound BSEGS ITC.
Proof. apply APS.mk_itab_ranges_sound. Qed.
(* [comment removed for export] *)
Definition NXC : nat := 344%nat.
Lemma NXC_ge : (NX0 <= NXC)%nat. Proof. unfold NX0, NXC. lia. Qed.
Definition startup_shapeC : shape := SCase (EVar 6) 10 (SCase e_atr8 17592186044384 (SHole 12) (SCase e_atr8 17592186044385 (SHole 12) (SCase e_atr8 17592186044386 (SHole 12) (SCase e_atr8 17592186044387 (SHole 12) (SCase e_atr8 17592186044388 (SHole 12) (SCase e_atr8 17592186044389 (SHole 12) (SCase e_atr8 17592186044390 (SHole 12) (SHole 12)))))))) (SCase e_atr8 17592186044384 (SHole 12) (SCase e_atr8 17592186044385 (SHole 12) (SCase e_atr8 17592186044386 (SHole 12) (SCase e_atr8 17592186044387 (SHole 12) (SCase e_atr8 17592186044388 (SHole 12) (SCase e_atr8 17592186044389 (SHole 12) (SCase e_atr8 17592186044390 (SHole 12) (SHole 12)))))))).
From Ltac2 Require Import Ltac2 Constr Std Control.
Ltac2 vm_cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
Lemma startup_certC :
  check BSEGS ITC ASAN NXC AsanInit.LIMIT (XNS BSEGS ASAN NXC AsanInit.LIMIT) XE0 XB0 HS_bothC KC0 BFUEL FUEL None HS_bothB_11 startup_plan_both_segB = COk startup_shapeC.
Proof. Time (vm_cert_refl constr:(COk startup_shapeC)). Time Qed.
