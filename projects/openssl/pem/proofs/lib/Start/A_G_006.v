(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 with the certificate lemma of this unit's Start/A_C_006.v, made once per value of the run's CONFIG_RSEQ flag, over the level's recorded plan in the new run's variable numbering, from that value's level-5 table, and with the hand-off table computed in the build at that value. *)
(* Start-up level 6, image A: the hand-off table computed from the level's start state, and the level's
   certificate over it (see PlanCoGen.v). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs PlanCoGen A_C_006 A_HS_005 A_HS_006 A_G_005.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* the start states are the computed per-build tables of level 5; this level's plan was generated
   against the recorded A_HS_005, so it runs behind a rename into that numbering *)
(* ONE TABLE PER KERNEL BUILD: this level runs from each build's own table and hands each build's
   arrival to its own table, because a table met over both builds drops every claim on the auxv tail
   (pairs 26-28 differ between the builds) and a later level reads it (the probe record of this port). *)
Definition A_mp_006_r0 : list (nat * nat) := Eval vm_compute in cg_map A_HS_005 A_HSg_005_r0.
Definition A_pl_006_r0 : plan := PRename A_mp_006_r0 A_plan_006.
Definition A_mp_006_r1 : list (nat * nat) := Eval vm_compute in cg_map A_HS_005 A_HSg_005_r1.
Definition A_pl_006_r1 : plan := PRename A_mp_006_r1 A_plan_006.
Definition A_chk_006 (cs : acs) (p : plan) (T : nat -> option acs) : cres :=
  check A_SEGS A_IT_006 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 T 0%nat 400000%nat 40000%nat None cs p.
Definition A_HSg_006_r0 : acs := Eval vm_compute in pc_next (pc_collect (A_chk_006 A_HSg_005_r0 A_pl_006_r0)) A_HS_006.
Definition A_HSg_006_r1 : acs := Eval vm_compute in pc_next (pc_collect (A_chk_006 A_HSg_005_r1 A_pl_006_r1)) A_HS_006.

Lemma A_cert_006_r0 :
  check A_SEGS A_IT_006 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HSg_006_r0) 0%nat 400000%nat 40000%nat None A_HSg_005_r0 A_pl_006_r0
  = COk A_shape_006.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_006)). Qed.

Lemma A_cert_006_r1 :
  check A_SEGS A_IT_006 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HSg_006_r1) 0%nat 400000%nat 40000%nat None A_HSg_005_r1 A_pl_006_r1
  = COk A_shape_006.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_006)). Qed.
