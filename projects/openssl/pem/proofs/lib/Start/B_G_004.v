(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 with the certificate lemma of this unit's Start/B_C_004.v, made once per value of the run's CONFIG_RSEQ flag, over the level's recorded plan in the new run's variable numbering, from that value's level-3 table, and with the hand-off table computed in the build at that value. *)
(* Start-up level 4, image B: the hand-off table computed from the level's start state, and the level's
   certificate over it (see PlanCoGen.v). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs PlanCoGen B_C_004 B_HS_003 B_HS_004 B_G_003.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* the start states are the computed per-build tables of level 3; this level's plan was generated
   against the recorded B_HS_003, so it runs behind a rename into that numbering *)
(* ONE TABLE PER KERNEL BUILD: this level runs from each build's own table and hands each build's
   arrival to its own table, because a table met over both builds drops every claim on the auxv tail
   (pairs 26-28 differ between the builds) and a later level reads it (the probe record of this port). *)
Definition B_mp_004_r0 : list (nat * nat) := Eval vm_compute in cg_map B_HS_003 B_HSg_003_r0.
Definition B_pl_004_r0 : plan := PRename B_mp_004_r0 B_plan_004.
Definition B_mp_004_r1 : list (nat * nat) := Eval vm_compute in cg_map B_HS_003 B_HSg_003_r1.
Definition B_pl_004_r1 : plan := PRename B_mp_004_r1 B_plan_004.
Definition B_chk_004 (cs : acs) (p : plan) (T : nat -> option acs) : cres :=
  check B_SEGS B_IT_004 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 T 0%nat 400000%nat 40000%nat None cs p.
Definition B_HSg_004_r0 : acs := Eval vm_compute in pc_next (pc_collect (B_chk_004 B_HSg_003_r0 B_pl_004_r0)) B_HS_004.
Definition B_HSg_004_r1 : acs := Eval vm_compute in pc_next (pc_collect (B_chk_004 B_HSg_003_r1 B_pl_004_r1)) B_HS_004.

Lemma B_cert_004_r0 :
  check B_SEGS B_IT_004 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HSg_004_r0) 0%nat 400000%nat 40000%nat None B_HSg_003_r0 B_pl_004_r0
  = COk B_shape_004.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_004)). Qed.

Lemma B_cert_004_r1 :
  check B_SEGS B_IT_004 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HSg_004_r1) 0%nat 400000%nat 40000%nat None B_HSg_003_r1 B_pl_004_r1
  = COk B_shape_004.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_004)). Qed.
