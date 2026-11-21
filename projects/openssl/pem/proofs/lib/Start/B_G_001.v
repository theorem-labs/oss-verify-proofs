(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 with the certificate lemma of this unit's Start/B_C_001.v, made once per value of the run's CONFIG_RSEQ flag, over the level's recorded plan in the new run's variable numbering, from that value's level-0 table, and with the hand-off table computed in the build at that value. *)
(* Start-up level 1, image B: the hand-off table computed from the level's start state, and the level's
   certificate over it (see PlanCoGen.v). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs PlanCoGen PlanRegen B_C_000 B_C_001 B_HS_000 B_HS_001.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* RE-SEEDED FROM LEVEL 0's COMPUTED TABLES, once per kernel build.  Level 0 hands off
   [B_HSg_000_r0] and [B_HSg_000_r1] (computed per build, B_C_000.v) where it used to hand off the
   recorded [B_HS_000], and this level's plan was generated against the recorded one.  [cg_map] aligns
   the two structurally and returns the [PRename] that puts each computed state into the recorded
   numbering; a wrong map can only make this level's [check] fail, and the certificates below are that
   check. *)
(* ONE TABLE PER KERNEL BUILD: this level runs from each build's own table and hands each build's
   arrival to its own table, because a table met over both builds drops every claim on the auxv tail
   (pairs 26-28 differ between the builds) and a later level reads it (the probe record of this port). *)
(* THE RENUMBERING, read off probes (the probe record of this port, rounds R7 and R9): the plan cut after each of its
   PRun nodes and run from the recorded B_HS_000 as recorded and, behind [cg_map], from each build's table reaches
   the same instructions with counters that differ from each threshold below on by the amount
   given there (a variable the recorded run numbered v the computed run numbers [B_vsh_001 v]). *)
Definition B_vsh_001 (v : nat) : nat := if Nat.ltb v 348 then v else (v + 2)%nat.
Definition B_mp_001_r0 : list (nat * nat) := Eval vm_compute in cg_map B_HS_000 B_HSg_000_r0.
Definition B_pl_001_r0 : plan := PRename B_mp_001_r0 (psh B_vsh_001 B_plan_001).
Definition B_mp_001_r1 : list (nat * nat) := Eval vm_compute in cg_map B_HS_000 B_HSg_000_r1.
Definition B_pl_001_r1 : plan := PRename B_mp_001_r1 (psh B_vsh_001 B_plan_001).
Definition B_chk_001 (cs : acs) (p : plan) (T : nat -> option acs) : cres :=
  check B_SEGS B_IT_001 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 T 0%nat 400000%nat 40000%nat None cs p.
Definition B_HSg_001_r0 : acs := Eval vm_compute in pc_next (pc_collect (B_chk_001 B_HSg_000_r0 B_pl_001_r0)) B_HS_001.
Definition B_HSg_001_r1 : acs := Eval vm_compute in pc_next (pc_collect (B_chk_001 B_HSg_000_r1 B_pl_001_r1)) B_HS_001.

Lemma B_cert_001_r0 :
  check B_SEGS B_IT_001 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HSg_001_r0) 0%nat 400000%nat 40000%nat None B_HSg_000_r0 B_pl_001_r0
  = COk B_shape_001.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_001)). Qed.

Lemma B_cert_001_r1 :
  check B_SEGS B_IT_001 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HSg_001_r1) 0%nat 400000%nat 40000%nat None B_HSg_000_r1 B_pl_001_r1
  = COk B_shape_001.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_001)). Qed.
