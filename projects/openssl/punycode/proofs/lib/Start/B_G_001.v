(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 with the certificate lemma of this unit's Start/B_C_001.v, made once per value of the run's CONFIG_RSEQ flag, over the level's recorded plan in the new run's variable numbering, from that value's level-0 table, and with the hand-off table computed in the build at that value. *)
(* Start-up level 1, image B: the recorded plan [B_plan_001], ONE CHAIN PER VALUE OF THE RUN'S CONFIG_RSEQ
   FLAG r (see Start/B_G_000.v): run from that value's own level-0 table computed in the build
   (Start/B_G_000.v), the level's hand-off table computed at that value alone, and its certificate. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs PlanCoGen PlanRegen B_C_001 B_HS_001 B_G_000.
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
Definition B_vsh_lv1 (v : nat) : nat := if Nat.ltb v 12 then v else if Nat.ltb v 348 then (v + 5)%nat else (v + 7)%nat.

(* r = 0 *)
Definition B_pl_001_r0 : plan := psh B_vsh_lv1 B_plan_001.
Definition B_chk_001_r0 (T : nat -> option acs) : cres :=
  check B_SEGS B_IT_001 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 T 0%nat 400000%nat 40000%nat None B_HSg_000_r0 B_pl_001_r0.
Definition B_R_001_r0 : pc_out := Eval vm_compute in pc_collect B_chk_001_r0.
Definition B_HSg_001_r0 : acs := Eval vm_compute in pc_next B_R_001_r0 B_HS_001.
Lemma B_cert_001_r0 :
  check B_SEGS B_IT_001 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HSg_001_r0) 0%nat 400000%nat 40000%nat None B_HSg_000_r0 B_pl_001_r0
  = COk B_shape_001.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_001)). Qed.

(* r = 1 *)
Definition B_pl_001_r1 : plan := psh B_vsh_lv1 B_plan_001.
Definition B_chk_001_r1 (T : nat -> option acs) : cres :=
  check B_SEGS B_IT_001 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 T 0%nat 400000%nat 40000%nat None B_HSg_000_r1 B_pl_001_r1.
Definition B_R_001_r1 : pc_out := Eval vm_compute in pc_collect B_chk_001_r1.
Definition B_HSg_001_r1 : acs := Eval vm_compute in pc_next B_R_001_r1 B_HS_001.
Lemma B_cert_001_r1 :
  check B_SEGS B_IT_001 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HSg_001_r1) 0%nat 400000%nat 40000%nat None B_HSg_000_r1 B_pl_001_r1
  = COk B_shape_001.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_001)). Qed.

