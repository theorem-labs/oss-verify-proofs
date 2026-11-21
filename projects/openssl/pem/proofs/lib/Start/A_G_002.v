(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 with the certificate lemma of this unit's Start/A_C_002.v, made once per value of the run's CONFIG_RSEQ flag, over the level's recorded plan in the new run's variable numbering, from that value's level-1 table, and with the hand-off table computed in the build at that value. *)
(* Start-up level 2, image A: the hand-off table computed from the level's start state, and the level's
   certificate over it (see PlanCoGen.v). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs PlanCoGen PlanRegen A_C_002 A_HS_001 A_HS_002 A_G_001.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* ONE TABLE PER KERNEL BUILD: this level runs from each build's own table and hands each build's
   arrival to its own table, because a table met over both builds drops every claim on the auxv tail
   (pairs 26-28 differ between the builds) and a later level reads it (the probe record of this port). *)
(* THE RENUMBERING, read off probes (the probe record of this port, round R9): the plan cut after each of its
   PRun nodes and run from the recorded A_HS_001 as recorded and from each build's table reaches
   the same instructions with counters that differ from each threshold below on by the amount
   given there (a variable the recorded run numbered v the computed run numbers [A_vsh_002 v]).
   The variables level 1 hands over keep that level's renumbering, which this map continues. *)
Definition A_vsh_002 (v : nat) : nat := if Nat.ltb v 348 then v else (v + 2)%nat.
Definition A_chk_002 (cs : acs) (p : plan) (T : nat -> option acs) : cres :=
  check A_SEGS A_IT_002 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 T 0%nat 400000%nat 40000%nat None cs p.
Definition A_HSg_002_r0 : acs := Eval vm_compute in pc_next (pc_collect (A_chk_002 A_HSg_001_r0 (psh A_vsh_002 A_plan_002))) A_HS_002.
Definition A_HSg_002_r1 : acs := Eval vm_compute in pc_next (pc_collect (A_chk_002 A_HSg_001_r1 (psh A_vsh_002 A_plan_002))) A_HS_002.

Lemma A_cert_002_r0 :
  check A_SEGS A_IT_002 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HSg_002_r0) 0%nat 400000%nat 40000%nat None A_HSg_001_r0 (psh A_vsh_002 A_plan_002)
  = COk A_shape_002.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_002)). Qed.

Lemma A_cert_002_r1 :
  check A_SEGS A_IT_002 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HSg_002_r1) 0%nat 400000%nat 40000%nat None A_HSg_001_r1 (psh A_vsh_002 A_plan_002)
  = COk A_shape_002.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_002)). Qed.
