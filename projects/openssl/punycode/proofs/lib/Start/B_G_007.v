(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 with the certificate lemma of this unit's Start/B_C_007.v, made once per value of the run's CONFIG_RSEQ flag, over the level's recorded plan in the new run's variable numbering, from that value's level-6 table, and with the hand-off table computed in the build at that value. *)
(* Start-up level 7, image B: the recorded plan [B_plan_007], ONE CHAIN PER VALUE OF THE RUN'S CONFIG_RSEQ
   FLAG r (see Start/B_G_000.v): run from that value's own level-6 table computed in the build
   (Start/B_G_006.v), the level's hand-off table computed at that value alone, and its certificate. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs PlanCoGen PlanRegen B_C_007 B_HS_007 B_HS_006 B_G_006.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* THE RENUMBERING: the start state is put into the numbering this level's plan was recorded against by
   PlanCoGen's [cg_map], which aligns main's recorded level-6 table with the computed one structurally and
   returns the [PRename] that renames the computed state; a wrong map can only make the certificate below fail.
   The form of openssl/pem's Start/A_G_001.v.  Round 10's probes: under one uniform shift the plan stops at a [PShDisj] (code 3, pc 1923028), under [cg_map] it closes (PZ-*-R*-L7).  Round 14's probe on the computed chain: under [cg_map] it closes at both r (PZ-*4-R*-L7). *)
(* r = 0 *)
Definition B_mp_007_r0 : list (nat * nat) := Eval vm_compute in cg_map B_HS_006 B_HSg_006_r0.
Definition B_pl_007_r0 : plan := PRename B_mp_007_r0 B_plan_007.
Definition B_chk_007_r0 (T : nat -> option acs) : cres :=
  check B_SEGS B_IT_007 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 T 0%nat 1500%nat 40000%nat None B_HSg_006_r0 B_pl_007_r0.
Definition B_R_007_r0 : pc_out := Eval vm_compute in pc_collect B_chk_007_r0.
Definition B_HSg_007_r0 : acs := Eval vm_compute in pc_next B_R_007_r0 B_HS_007.
Lemma B_cert_007_r0 :
  check B_SEGS B_IT_007 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HSg_007_r0) 0%nat 1500%nat 40000%nat None B_HSg_006_r0 B_pl_007_r0
  = COk B_shape_007.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_007)). Qed.

(* r = 1 *)
Definition B_mp_007_r1 : list (nat * nat) := Eval vm_compute in cg_map B_HS_006 B_HSg_006_r1.
Definition B_pl_007_r1 : plan := PRename B_mp_007_r1 B_plan_007.
Definition B_chk_007_r1 (T : nat -> option acs) : cres :=
  check B_SEGS B_IT_007 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 T 0%nat 1500%nat 40000%nat None B_HSg_006_r1 B_pl_007_r1.
Definition B_R_007_r1 : pc_out := Eval vm_compute in pc_collect B_chk_007_r1.
Definition B_HSg_007_r1 : acs := Eval vm_compute in pc_next B_R_007_r1 B_HS_007.
Lemma B_cert_007_r1 :
  check B_SEGS B_IT_007 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HSg_007_r1) 0%nat 1500%nat 40000%nat None B_HSg_006_r1 B_pl_007_r1
  = COk B_shape_007.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_007)). Qed.

