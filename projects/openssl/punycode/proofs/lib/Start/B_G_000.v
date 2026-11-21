(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 with the certificate lemma of this unit's Start/B_C_000.v, made once per value of the run's CONFIG_RSEQ flag, over the level's recorded plan renumbered by Start/PlanRegen.v's psh, from the start state at that value, and with the hand-off table computed in the build at that value. *)
(* Start-up level 0, image B: the recorded plan [B_plan_000] renumbered where it is checked
   (Start/PlanRegen.v's [psh]), and ONE CHAIN PER VALUE OF THE RUN'S CONFIG_RSEQ FLAG r: the level's hand-off
   table computed in the build at each value alone (Start/PlanCoGen.v's [pc_go]) and its certificate.  The two
   tables differ in the auxv pairs from 26 on (CONFIG_RSEQ's two pairs, then AT_NULL), which musl's walks of the
   auxv read at the next levels; one table met from both values loses them.  The form of openssl/pem's
   Start/A_C_000.v, with the renumbering by [psh] instead of literals edited in the plan text. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs PlanCoGen PlanRegen B_C_000 B_HS_000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* THE RENUMBERING, read off a probe, not chosen (the probe record of this port, level 0): the recorded
   plan, run unshifted at r = 0 and r = 1, stops at its first [PShDisj] with the new map [4096 * EVar 105, 65536]
   where the plan names [EVar 100], so old 100 is new 105; the plan renumbered by +5 reaches [PHandoff 0] at both
   values.  The recorded plan is in main's numbering, whose NX0 was 12: the launch variables below 12 keep their
   numbers (V_G, V_R and V_GID are 12, 13, 14 now), every fresh variable moves by +5.  The plan names no variable
   between 12 and 99, so this is the probe's [vshift 14 5] on it. *)
Definition B_vsh_000 : nat -> nat := vshift 12 5.
Definition B_pl_000 : plan := psh B_vsh_000 B_plan_000.

Definition B_chk_000 (r : Z) (T : nat -> option acs) : cres :=
  check B_SEGS B_IT_000 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 T 0%nat 400000%nat 40000%nat None (init_acs_of r B_T) B_pl_000.
(* [pc_next]'s fallback is the recorded [B_HS_000], which the certificates would then reject. *)
Definition B_R_000_r0 : pc_out := Eval vm_compute in pc_go (B_chk_000 0) 16 None [].
Definition B_HSg_000_r0 : acs := Eval vm_compute in pc_next B_R_000_r0 B_HS_000.
Definition B_R_000_r1 : pc_out := Eval vm_compute in pc_go (B_chk_000 1) 16 None [].
Definition B_HSg_000_r1 : acs := Eval vm_compute in pc_next B_R_000_r1 B_HS_000.

Lemma B_cert_000_r0 :
  check B_SEGS B_IT_000 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HSg_000_r0) 0%nat 400000%nat 40000%nat None (init_acs_of 0 B_T) B_pl_000
  = COk B_shape_000.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_000)). Qed.

Lemma B_cert_000_r1 :
  check B_SEGS B_IT_000 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HSg_000_r1) 0%nat 400000%nat 40000%nat None (init_acs_of 1 B_T) B_pl_000
  = COk B_shape_000.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_000)). Qed.
