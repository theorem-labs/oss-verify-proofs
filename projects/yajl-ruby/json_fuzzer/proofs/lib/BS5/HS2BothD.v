(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from HS2Both.v as in the LPS 727298f3 update: the S2 run's definitions (its start counter, extension hooks, instruction table, renumbered plan, start states read from the S1 hand-off tables of CertS1BothT.v, and the check, also run once with a collector at its hand-offs), split from the hand-off tables (HS2BothT0a/T0b/T1a/T1b.v) so the four tables build in parallel. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanInit PlanRegen.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import A_Hooks5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.BS5 Require Import AsanPlanImagesB PlanS2Both CertS1BothT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* S2 runs from each S1 hand-off state (CertS1BothT.HS_s1) to the main phase's hand-offs 0 and 1.
   Its plan names fresh variables of the S1 run (EVar 374) and starts its own at the S1 hand-off
   states' counter, so it is renumbered by the S1 map. *)
Definition N2 : nat := vsh1 514.
Definition XN2 := A_Hooks5.XN5 BSEGS BOTH5 N2.
Definition IT2 : itab := mk_itab_ranges BSEGS s2_plan_ranges.
Definition s2_plan_k : plan := psh vsh1 s2_plan.
Definition s2_start (r : Z) (h : nat) : acs := hstate (fst (S1C r)) (init_acs_of r BOTH5) h.
Definition s2_run (r : Z) (h : nat) (H : nat -> option acs) : cres :=
  check BSEGS IT2 BOTH5 N2 AsanInit.LIMIT r XN2 XE0 XB0 H KC0 BFUEL FUEL None (s2_start r h) s2_plan_k.

(* [s2_coll] is [s2_run]'s check written as [check_coll], which hands each state it reaches at a
   hand-off to [hvisit], so one run makes the map [collect_handoffs] makes in one run per state.
   The S2 plan has no via, so [check_coll]'s join collector is never called. *)
Definition s2_coll (r : Z) (h : nat) (bm : nat * list (nat * acs)) : cres * (nat * list (nat * acs)) :=
  check_coll BSEGS IT2 BOTH5 N2 AsanInit.LIMIT r XN2 XE0 XB0 KC0 BFUEL _ hvisit (fun _ _ _ m => m) (fun _ _ => None)
    FUEL None (s2_start r h) s2_plan_k bm.
