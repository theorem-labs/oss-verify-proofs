(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the S2 certificates per CONFIG_RSEQ value, from the computed S1 hand-off states to the computed main-phase entry states, the plan renumbered where it is checked; the certificates are stated as the check run itself, in the form the start-up's soundness lemma takes). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl PlanRegen.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import A_Hooks5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import AsanPlanImagesB PlanS2Both CertS1Both HS2Both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma N2_ge : (NX0 <= N2)%nat.
Proof. unfold NX0. apply Nat.leb_le. vm_compute. reflexivity. Qed.

Lemma IT2_ok : AX2.itab_sound BSEGS IT2.
Proof. apply APS.mk_itab_ranges_sound. Qed.

(* [comment removed for export] *)
Definition s2_shape : shape :=
  shsh vsh1 (SCase (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 374))) 3935) 4030 (SHole 0) (SHole 1)).

(* LPS 727298f3: the S2 certificates are stated as the check run itself, in the form the start-up's
   check-soundness lemma takes; stated through s2_run, a certificate met that premise only through a
   conversion the kernel settled by reducing check itself, for hours. *)
#[local] Notation S2CHK r h H :=
  (check BSEGS IT2 BOTH5 N2 AsanInit.LIMIT r (A_Hooks5.XN5 BSEGS BOTH5 N2) XE0 XB0 H CertS1BothD.KC0 BFUEL FUEL None (s2_start r h) s2_plan_k).

Lemma s2_cert_a0 : S2CHK 0 0%nat (HS_s2a 0) = COk s2_shape.
Proof. ltac2:(cert_refl_vm constr:(COk s2_shape)). Qed.
Lemma s2_cert_a1 : S2CHK 1 0%nat (HS_s2a 1) = COk s2_shape.
Proof. ltac2:(cert_refl_vm constr:(COk s2_shape)). Qed.
Lemma s2_cert_b0 : S2CHK 0 1%nat (HS_s2b 0) = COk s2_shape.
Proof. ltac2:(cert_refl_vm constr:(COk s2_shape)). Qed.
Lemma s2_cert_b1 : S2CHK 1 1%nat (HS_s2b 1) = COk s2_shape.
Proof. ltac2:(cert_refl_vm constr:(COk s2_shape)). Qed.

Lemma s2_cert_a : forall b : bool, S2CHK (rseq_z b) 0%nat (HS_s2a (rseq_z b)) = COk s2_shape.
Proof. intros [|]; [exact s2_cert_a1 | exact s2_cert_a0]. Qed.
Lemma s2_cert_b : forall b : bool, S2CHK (rseq_z b) 1%nat (HS_s2b (rseq_z b)) = COk s2_shape.
Proof. intros [|]; [exact s2_cert_b1 | exact s2_cert_b0]. Qed.
