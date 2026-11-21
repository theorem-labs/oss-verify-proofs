(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 with the certificate lemma of this unit's Start/A_C_003.v, made once per value of the run's CONFIG_RSEQ flag, over the level's recorded plan in the new run's variable numbering, from that value's level-2 table, and with the hand-off table computed in the build at that value by Start/PlanCoGen.v's join pc_collect_j. *)
(* Start-up level 3, image A: the recorded plan [A_plan_003], ONE CHAIN PER VALUE OF THE RUN'S CONFIG_RSEQ
   FLAG r (see Start/A_G_000.v): run from that value's own level-2 table computed in the build
   (Start/A_G_002.v), the level's hand-off table computed at that value alone, and its certificate. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs PlanCoGen PlanRegen A_C_003 A_HS_003 A_G_001 A_G_002.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* The renumbering is level 1's (Start/A_G_001.v: +5 below the old 348, +7 from it on): run from each r's computed
   level-2 table, this level closes under it at both r, allocating as the recorded run did (round 14's probe on
   the computed chain in the probe record of this port, PZ-*4-R*-L3: nxt 565 against main's 558), so the
   variables it names keep level 1's map.
   The level reaches its hand-off twice, and the two arrivals hold the ASan stack-depot count as the literals 3 and
   2 (and the words derived from it as other literals; round 17's probe, PZ-*7-CMP1/2).  The table is collected
   with Start/PlanCoGen.v's [pc_collect_j], whose join generalises those words into one fresh variable with the
   range the two arrivals give, where [pc_collect]'s meet would drop them; the certificate re-checks both
   arrivals against it. *)
(* r = 0 *)
Definition A_pl_003_r0 : plan := psh A_vsh_lv1 A_plan_003.
Definition A_chk_003_r0 (T : nat -> option acs) : cres :=
  check A_SEGS A_IT_003 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 T 0%nat 400000%nat 40000%nat None A_HSg_002_r0 A_pl_003_r0.
Definition A_R_003_r0 : pc_out := Eval vm_compute in pc_collect_j A_T A_chk_003_r0.
Definition A_HSg_003_r0 : acs := Eval vm_compute in pc_next A_R_003_r0 A_HS_003.
Lemma A_cert_003_r0 :
  check A_SEGS A_IT_003 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HSg_003_r0) 0%nat 400000%nat 40000%nat None A_HSg_002_r0 A_pl_003_r0
  = COk A_shape_003.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_003)). Qed.

(* r = 1 *)
Definition A_pl_003_r1 : plan := psh A_vsh_lv1 A_plan_003.
Definition A_chk_003_r1 (T : nat -> option acs) : cres :=
  check A_SEGS A_IT_003 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 T 0%nat 400000%nat 40000%nat None A_HSg_002_r1 A_pl_003_r1.
Definition A_R_003_r1 : pc_out := Eval vm_compute in pc_collect_j A_T A_chk_003_r1.
Definition A_HSg_003_r1 : acs := Eval vm_compute in pc_next A_R_003_r1 A_HS_003.
Lemma A_cert_003_r1 :
  check A_SEGS A_IT_003 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HSg_003_r1) 0%nat 400000%nat 40000%nat None A_HSg_002_r1 A_pl_003_r1
  = COk A_shape_003.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_003)). Qed.

