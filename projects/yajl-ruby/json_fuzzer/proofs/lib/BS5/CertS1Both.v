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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import AsanPlanImagesB PlanS1Both JS1Both HS1Both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Open Scope Z_scope.

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
Definition XN0 := A_Hooks5.XN5 BSEGS BOTH5 NX0.

(* [comment removed for export] *)
Definition IT1 : itab := mk_itab_ranges BSEGS s1_plan_ranges.
Lemma IT1_ok : AX2.itab_sound BSEGS IT1.
Proof. apply APS.mk_itab_ranges_sound. Qed.

Definition s1_shape : shape :=
  SCase (EVar 6) 10
    (SCase (EVar 10) 0 (SCase (EVar 5) 524277 (SHole 0) (SHole 1))
       (SCase (EVar 10) 6 (SCase (EVar 5) 524277 (SHole 0) (SHole 1)) (SCase (EVar 5) 524277 (SHole 0) (SHole 1))))
    (SCase (EVar 10) 0 (SCase (EVar 5) 524277 (SHole 0) (SHole 1))
       (SCase (EVar 10) 6 (SCase (EVar 5) 524277 (SHole 0) (SHole 1)) (SCase (EVar 5) 524277 (SHole 0) (SHole 1)))).

Lemma s1_cert :
  check BSEGS IT1 BOTH5 NX0 AsanInit.LIMIT XN0 XE0 XB0 HS_s1 KC0 BFUEL FUEL None (init_acs_of BOTH5) (s1_plan js_2 js_11) = COk s1_shape.
Proof. ltac2:(cert_refl_vm constr:(COk s1_shape)). Qed.
