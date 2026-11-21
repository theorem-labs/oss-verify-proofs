(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the recorded hand-off states replaced by the states seg90 reaches at LPS 727298f3, computed in the build, one per CONFIG_RSEQ value; the plan renumbered by a map read from a probe. *)
(* [comment removed for export] *)

(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsHSTab
  AsImages AsPlanImages AsStartup AsStartupPlan AsStartupRanges AsPlanRegen AsStartupHS1.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

(* LPS 727298f3: the states at hand-offs 91 and 94, computed in the build from each CONFIG_RSEQ
   value's state at 90; seg90 renumbered by [vsh_90] (a probe of the run: at seg90's PRangeGaps 326 the run's new region is 4096 * EVar 333, so old 326 is new 333; with this map seg90 reaches 91 and 94 at both values with the fresh counter at 367 = 360 + 7). *)
Definition vsh_90 : nat -> nat := tshift [(13%nat, 5%nat); (326%nat, 7%nat)].
Definition startup_plan_seg90_k : plan := psh vsh_90 startup_plan_seg90.
Definition seg90_run (s : acs) (T : nat -> option acs) : cres :=
  check ASEGS (mk_itab_ranges ASEGS startup_plan_seg90_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 T CERT_KC0 CERT_BFUEL CERT_FUEL None s startup_plan_seg90_k.
Definition HSC_asan_list_0 : list (nat * acs) := Eval vm_compute in collect_k 6 (seg90_run HS1_asan_90_0) [].
Definition HSC_asan_list_1 : list (nat * acs) := Eval vm_compute in collect_k 6 (seg90_run HS1_asan_90_1) [].
Definition HSC_asan_91_0 : acs := Eval vm_compute in hstate HSC_asan_list_0 HS1_asan_90_0 91.
Definition HSC_asan_94_0 : acs := Eval vm_compute in hstate HSC_asan_list_0 HS1_asan_90_0 94.
Definition HSC_asan_91_1 : acs := Eval vm_compute in hstate HSC_asan_list_1 HS1_asan_90_1 91.
Definition HSC_asan_94_1 : acs := Eval vm_compute in hstate HSC_asan_list_1 HS1_asan_90_1 94.
Definition HSC_asan_table_0 : list (nat * acs) := [(91%nat, HSC_asan_91_0); (94%nat, HSC_asan_94_0)].
Definition HSC_asan_table_1 : list (nat * acs) := [(91%nat, HSC_asan_91_1); (94%nat, HSC_asan_94_1)].
Definition HSC_asan_0 (h : nat) : option acs := hs_lookup h HSC_asan_table_0.
Definition HSC_asan_1 (h : nat) : option acs := hs_lookup h HSC_asan_table_1.
Definition HSC_asan_r (r : Z) : nat -> option acs := if Z.eqb r 1 then HSC_asan_1 else HSC_asan_0.
