(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 with the certificate lemma of this unit's Start/A_C_001.v, made once per value of the run's CONFIG_RSEQ flag, over the level's recorded plan in the new run's variable numbering, from that value's level-0 table, and with the hand-off table computed in the build at that value. *)
(* Start-up level 1, image A: the recorded plan [A_plan_001], ONE CHAIN PER VALUE OF THE RUN'S CONFIG_RSEQ
   FLAG r (see Start/A_G_000.v): run from that value's own level-0 table computed in the build
   (Start/A_G_000.v), the level's hand-off table computed at that value alone, and its certificate. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs PlanCoGen PlanRegen A_C_001 A_HS_001 A_G_000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* THE RENUMBERING, read off probes, not chosen (the probe record of this port, level 1): the plan cut after
   each of its PRun nodes and run from main's recorded table and from the computed one (shifted by +5) reaches the
   same instructions with counters 283, 284, 300, 316, 332, 348, ... against 288, 289, 305, 321, 337, 355: +5 up
   to the plan's fourth PRun, +7 from its second mmap on, whose result the computed run holds as [EVar 355] where
   the plan names [EVar 348] (two more fresh reads in between than the recorded run made).  The plan names, above
   the launch's variables, only 283 (+5) and 348, 349, 382 (+7). *)
Definition A_vsh_lv1 (v : nat) : nat := if Nat.ltb v 12 then v else if Nat.ltb v 348 then (v + 5)%nat else (v + 7)%nat.

(* r = 0 *)
Definition A_pl_001_r0 : plan := psh A_vsh_lv1 A_plan_001.
Definition A_chk_001_r0 (T : nat -> option acs) : cres :=
  check A_SEGS A_IT_001 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 T 0%nat 400000%nat 40000%nat None A_HSg_000_r0 A_pl_001_r0.
Definition A_R_001_r0 : pc_out := Eval vm_compute in pc_collect A_chk_001_r0.
Definition A_HSg_001_r0 : acs := Eval vm_compute in pc_next A_R_001_r0 A_HS_001.
Lemma A_cert_001_r0 :
  check A_SEGS A_IT_001 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HSg_001_r0) 0%nat 400000%nat 40000%nat None A_HSg_000_r0 A_pl_001_r0
  = COk A_shape_001.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_001)). Qed.

(* r = 1 *)
Definition A_pl_001_r1 : plan := psh A_vsh_lv1 A_plan_001.
Definition A_chk_001_r1 (T : nat -> option acs) : cres :=
  check A_SEGS A_IT_001 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 T 0%nat 400000%nat 40000%nat None A_HSg_000_r1 A_pl_001_r1.
Definition A_R_001_r1 : pc_out := Eval vm_compute in pc_collect A_chk_001_r1.
Definition A_HSg_001_r1 : acs := Eval vm_compute in pc_next A_R_001_r1 A_HS_001.
Lemma A_cert_001_r1 :
  check A_SEGS A_IT_001 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HSg_001_r1) 0%nat 400000%nat 40000%nat None A_HSg_000_r1 A_pl_001_r1
  = COk A_shape_001.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_001)). Qed.

