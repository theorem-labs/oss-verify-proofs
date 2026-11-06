(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import A_Hooks5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import AsanPlanImagesB PlanS2Both HS1Both HS2Both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Open Scope Z_scope.

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
(* [comment removed for export] *)
Definition N2 : nat := 514.
Lemma N2_nxt : nxt HS_s1_0 = N2 /\ nxt HS_s1_1 = N2.
Proof. split; reflexivity. Qed.
Lemma N2_ge : (NX0 <= N2)%nat.
Proof. unfold NX0, N2. apply Nat.leb_le. reflexivity. Qed.
Definition XN2 := A_Hooks5.XN5 BSEGS BOTH5 N2.

Definition IT2 : itab := mk_itab_ranges BSEGS s2_plan_ranges.
Lemma IT2_ok : AX2.itab_sound BSEGS IT2.
Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition s2_shape : shape := SCase (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 374))) 3935) 4030 (SHole 0) (SHole 1).

Lemma s2_cert_0 :
  check BSEGS IT2 BOTH5 N2 AsanInit.LIMIT XN2 XE0 XB0 HS_s2a KC0 BFUEL FUEL None HS_s1_0 s2_plan = COk s2_shape.
Proof. ltac2:(cert_refl_vm constr:(COk s2_shape)). Qed.

Lemma s2_cert_1 :
  check BSEGS IT2 BOTH5 N2 AsanInit.LIMIT XN2 XE0 XB0 HS_s2b KC0 BFUEL FUEL None HS_s1_1 s2_plan = COk s2_shape.
Proof. ltac2:(cert_refl_vm constr:(COk s2_shape)). Qed.
