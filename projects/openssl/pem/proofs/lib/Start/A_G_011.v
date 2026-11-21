(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 with the certificate lemma of this unit's Start/A_C_011.v, made once per value of the run's CONFIG_RSEQ flag, over the level's recorded plan in the new run's variable numbering, from that value's level-10 table, and with the one hand-off table computed in the build from both values. *)
(* Start-up level 11, image A: the hand-off table computed from the level's start state, and the level's
   certificate over it (see PlanCoGen.v). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs PlanCoGen A_C_011 A_HS_010 A_HS_011 A_G_010.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* the start states are the computed per-build tables of level 10; this level's plan was generated
   against the recorded A_HS_010, so it runs behind a rename into that numbering *)
(* Run once per kernel build from that build's table; this level's own hand-off table, the main hand-off
   [A_HSm], is collected over BOTH builds' arrivals (r = 0 first, r = 1 once r = 0 accepts;
   [PlanCoGen.pc_meet] at a second arrival).  Fuel 16 because two builds arrive. *)
Definition A_mp_011_r0 : list (nat * nat) := Eval vm_compute in cg_map A_HS_010 A_HSg_010_r0.
Definition A_pl_011_r0 : plan := PRename A_mp_011_r0 A_plan_011.
Definition A_mp_011_r1 : list (nat * nat) := Eval vm_compute in cg_map A_HS_010 A_HSg_010_r1.
Definition A_pl_011_r1 : plan := PRename A_mp_011_r1 A_plan_011.
Definition A_chk_011 (cs : acs) (p : plan) (T : nat -> option acs) : cres :=
  check A_SEGS A_IT_011 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 T 0%nat 400000%nat 40000%nat None cs p.
Definition A_R_011 : pc_out := Eval vm_compute in
  pc_go (fun T => match A_chk_011 A_HSg_010_r0 A_pl_011_r0 T with
                  | COk _ => A_chk_011 A_HSg_010_r1 A_pl_011_r1 T | e => e end) 16 None [].
Definition A_HSg_011 : acs := Eval vm_compute in pc_next A_R_011 A_HS_011.

Lemma A_cert_011_r0 :
  check A_SEGS A_IT_011 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HSg_011) 0%nat 400000%nat 40000%nat None A_HSg_010_r0 A_pl_011_r0
  = COk A_shape_011.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_011)). Qed.

Lemma A_cert_011_r1 :
  check A_SEGS A_IT_011 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HSg_011) 0%nat 400000%nat 40000%nat None A_HSg_010_r1 A_pl_011_r1
  = COk A_shape_011.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_011)). Qed.
