(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 with the certificate lemma of this unit's Start/B_C_011.v, made once per value of the run's CONFIG_RSEQ flag, over the level's recorded plan in the new run's variable numbering, from that value's level-10 table, and with the one hand-off table computed in the build from both values. *)
(* Start-up level 11, image B: the hand-off table computed from the level's start state, and the level's
   certificate over it (see PlanCoGen.v). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs PlanCoGen B_C_011 B_HS_010 B_HS_011 B_G_010.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* the start states are the computed per-build tables of level 10; this level's plan was generated
   against the recorded B_HS_010, so it runs behind a rename into that numbering *)
(* Run once per kernel build from that build's table; this level's own hand-off table, the main hand-off
   [B_HSm], is collected over BOTH builds' arrivals (r = 0 first, r = 1 once r = 0 accepts;
   [PlanCoGen.pc_meet] at a second arrival).  Fuel 16 because two builds arrive. *)
Definition B_mp_011_r0 : list (nat * nat) := Eval vm_compute in cg_map B_HS_010 B_HSg_010_r0.
Definition B_pl_011_r0 : plan := PRename B_mp_011_r0 B_plan_011.
Definition B_mp_011_r1 : list (nat * nat) := Eval vm_compute in cg_map B_HS_010 B_HSg_010_r1.
Definition B_pl_011_r1 : plan := PRename B_mp_011_r1 B_plan_011.
Definition B_chk_011 (cs : acs) (p : plan) (T : nat -> option acs) : cres :=
  check B_SEGS B_IT_011 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 T 0%nat 400000%nat 40000%nat None cs p.
Definition B_R_011 : pc_out := Eval vm_compute in
  pc_go (fun T => match B_chk_011 B_HSg_010_r0 B_pl_011_r0 T with
                  | COk _ => B_chk_011 B_HSg_010_r1 B_pl_011_r1 T | e => e end) 16 None [].
Definition B_HSg_011 : acs := Eval vm_compute in pc_next B_R_011 B_HS_011.

Lemma B_cert_011_r0 :
  check B_SEGS B_IT_011 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HSg_011) 0%nat 400000%nat 40000%nat None B_HSg_010_r0 B_pl_011_r0
  = COk B_shape_011.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_011)). Qed.

Lemma B_cert_011_r1 :
  check B_SEGS B_IT_011 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HSg_011) 0%nat 400000%nat 40000%nat None B_HSg_010_r1 B_pl_011_r1
  = COk B_shape_011.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_011)). Qed.
