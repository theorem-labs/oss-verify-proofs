(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 with the certificate lemma of this unit's Start/A_C_004.v, made once per value of the run's CONFIG_RSEQ flag, over the level's recorded plan in the new run's variable numbering, from that value's level-3 table, and with the hand-off table computed in the build at that value. *)
(* Start-up level 4, image A: the recorded plan [A_plan_004], ONE CHAIN PER VALUE OF THE RUN'S CONFIG_RSEQ
   FLAG r (see Start/A_G_000.v): run from that value's own level-3 table computed in the build
   (Start/A_G_003.v), the level's hand-off table computed at that value alone, and its certificate. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs PlanCoGen PlanRegen A_C_004 A_HS_004 A_G_001 A_G_003.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* The renumbering is level 1's (A_G_001.v: +5 below the old 348, +7 from it on): run from each r's computed
   level-3 table, this level closes under it at both r, allocating as the recorded run did (round 14's probe on
   the computed chain in the probe record of this port, PZ-*4-R*-L4: nxt 56 against main's 55), so the
   variables it names keep level 1's map. *)
(* r = 0 *)
Definition A_pl_004_r0 : plan := psh A_vsh_lv1 A_plan_004.
Definition A_chk_004_r0 (T : nat -> option acs) : cres :=
  check A_SEGS A_IT_004 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 T 0%nat 400000%nat 40000%nat None A_HSg_003_r0 A_pl_004_r0.
Definition A_R_004_r0 : pc_out := Eval vm_compute in pc_collect A_chk_004_r0.
Definition A_HSg_004_r0 : acs := Eval vm_compute in pc_next A_R_004_r0 A_HS_004.
Lemma A_cert_004_r0 :
  check A_SEGS A_IT_004 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HSg_004_r0) 0%nat 400000%nat 40000%nat None A_HSg_003_r0 A_pl_004_r0
  = COk A_shape_004.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_004)). Qed.

(* r = 1 *)
Definition A_pl_004_r1 : plan := psh A_vsh_lv1 A_plan_004.
Definition A_chk_004_r1 (T : nat -> option acs) : cres :=
  check A_SEGS A_IT_004 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 T 0%nat 400000%nat 40000%nat None A_HSg_003_r1 A_pl_004_r1.
Definition A_R_004_r1 : pc_out := Eval vm_compute in pc_collect A_chk_004_r1.
Definition A_HSg_004_r1 : acs := Eval vm_compute in pc_next A_R_004_r1 A_HS_004.
Lemma A_cert_004_r1 :
  check A_SEGS A_IT_004 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HSg_004_r1) 0%nat 400000%nat 40000%nat None A_HSg_003_r1 A_pl_004_r1
  = COk A_shape_004.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_004)). Qed.

