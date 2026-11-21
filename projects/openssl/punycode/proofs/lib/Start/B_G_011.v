(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 with the certificate lemma of this unit's Start/B_C_011.v, made once per value of the run's CONFIG_RSEQ flag, over the level's recorded plan in the new run's variable numbering, from that value's level-10 table, and with the one hand-off table computed in the build from both values. *)
(* Start-up level 11, image B, the last: the recorded plan [B_plan_011] renumbered where it is checked, run
   from each chain's level-10 table computed in the build (Start/B_G_010.v).  The two chains (one per value of
   the run's CONFIG_RSEQ flag r, Start/B_G_000.v) meet here: ONE hand-off table is computed from both level-10
   tables (r = 0 first, r = 1 once r = 0 accepts, so every state arriving at [PHandoff 0] from either chain is
   recorded or met with the table so far), and each chain's certificate re-checks it.  Start/B_Chain.v ends both
   chains at this table. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs PlanCoGen PlanRegen B_C_011 B_HS_011 B_G_010.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* The renumbering, read off a probe, not chosen (the probe record of this port, level 11): round 10's probes: from the level-10 tables this level closed under the shift its counters give, +1 (computed nxt 57 against main's 56), from each chain and from both into one table (PZ-*-R*-L11, PZ-*-M11); round 14's probe on the computed chain: from both chains' level-10 tables into one table it closes under +1 (PZ-*4-M11). *)
Definition B_vsh_011 : nat -> nat := vshift 12 1.
Definition B_pl_011 : plan := psh B_vsh_011 B_plan_011.
Definition B_chk_011_r0 (T : nat -> option acs) : cres :=
  check B_SEGS B_IT_011 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 T 0%nat 400000%nat 40000%nat None B_HSg_010_r0 B_pl_011.
Definition B_chk_011_r1 (T : nat -> option acs) : cres :=
  check B_SEGS B_IT_011 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 T 0%nat 400000%nat 40000%nat None B_HSg_010_r1 B_pl_011.

Definition B_R_011 : pc_out := Eval vm_compute in
  pc_go (fun T => match B_chk_011_r0 T with COk _ => B_chk_011_r1 T | e => e end) 16 None [].
Definition B_HSg_011 : acs := Eval vm_compute in pc_next B_R_011 B_HS_011.

Lemma B_cert_011_r0 :
  check B_SEGS B_IT_011 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HSg_011) 0%nat 400000%nat 40000%nat None B_HSg_010_r0 B_pl_011
  = COk B_shape_011.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_011)). Qed.

Lemma B_cert_011_r1 :
  check B_SEGS B_IT_011 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HSg_011) 0%nat 400000%nat 40000%nat None B_HSg_010_r1 B_pl_011
  = COk B_shape_011.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_011)). Qed.

