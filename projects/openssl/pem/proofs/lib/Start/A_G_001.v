(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 with the certificate lemma of this unit's Start/A_C_001.v, made once per value of the run's CONFIG_RSEQ flag, over the level's recorded plan in the new run's variable numbering, from that value's level-0 table, and with the hand-off table computed in the build at that value. *)
(* Start-up level 1, image A: the hand-off table computed from the level's start state, and the level's
   certificate over it (see PlanCoGen.v). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs PlanCoGen PlanRegen A_C_000 A_C_001 A_HS_000 A_HS_001.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* RE-SEEDED FROM LEVEL 0's COMPUTED TABLES, once per kernel build.  Level 0 hands off
   [A_HSg_000_r0] and [A_HSg_000_r1] (computed per build, A_C_000.v) where it used to hand off the
   recorded [A_HS_000], and this level's plan was generated against the recorded one.  [cg_map] aligns
   the two structurally and returns the [PRename] that puts each computed state into the recorded
   numbering; a wrong map can only make this level's [check] fail, and the certificates below are that
   check. *)
(* ONE TABLE PER KERNEL BUILD: this level runs from each build's own table and hands each build's
   arrival to its own table, because a table met over both builds drops every claim on the auxv tail
   (pairs 26-28 differ between the builds) and a later level reads it (the probe record of this port). *)
(* THE RENUMBERING, read off probes (the probe record of this port, rounds R7 and R9): the plan cut after each of its
   PRun nodes and run from the recorded A_HS_000 as recorded and, behind [cg_map], from each build's table reaches
   the same instructions with counters that differ from each threshold below on by the amount
   given there (a variable the recorded run numbered v the computed run numbers [A_vsh_001 v]). *)
Definition A_vsh_001 (v : nat) : nat := if Nat.ltb v 348 then v else (v + 2)%nat.
Definition A_mp_001_r0 : list (nat * nat) := Eval vm_compute in cg_map A_HS_000 A_HSg_000_r0.
Definition A_pl_001_r0 : plan := PRename A_mp_001_r0 (psh A_vsh_001 A_plan_001).
Definition A_mp_001_r1 : list (nat * nat) := Eval vm_compute in cg_map A_HS_000 A_HSg_000_r1.
Definition A_pl_001_r1 : plan := PRename A_mp_001_r1 (psh A_vsh_001 A_plan_001).
Definition A_chk_001 (cs : acs) (p : plan) (T : nat -> option acs) : cres :=
  check A_SEGS A_IT_001 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 T 0%nat 400000%nat 40000%nat None cs p.
Definition A_HSg_001_r0 : acs := Eval vm_compute in pc_next (pc_collect (A_chk_001 A_HSg_000_r0 A_pl_001_r0)) A_HS_001.
Definition A_HSg_001_r1 : acs := Eval vm_compute in pc_next (pc_collect (A_chk_001 A_HSg_000_r1 A_pl_001_r1)) A_HS_001.

Lemma A_cert_001_r0 :
  check A_SEGS A_IT_001 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HSg_001_r0) 0%nat 400000%nat 40000%nat None A_HSg_000_r0 A_pl_001_r0
  = COk A_shape_001.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_001)). Qed.

Lemma A_cert_001_r1 :
  check A_SEGS A_IT_001 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HSg_001_r1) 0%nat 400000%nat 40000%nat None A_HSg_000_r1 A_pl_001_r1
  = COk A_shape_001.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_001)). Qed.
