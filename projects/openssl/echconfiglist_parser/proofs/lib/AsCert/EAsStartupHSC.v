(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the recorded hand-off states replaced by the states seg90 reaches at LPS 727298f3, computed in the build, one per CONFIG_RSEQ value; the plan renumbered by a map read from a probe. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanInit AsHSTab AsPlanRegen.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.AsCert Require Import AsImages AsPlanImages AsStartup EAsStartupPlan EAsStartupRanges EAsStartupHS1.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* LPS 727298f3: the states at hand-offs 91 and 94, computed in the build from each CONFIG_RSEQ value's
   state at 90; seg90 renumbered by [vsh_90_r] (from each value's state at 90 the seg90 plan's PRangeGaps names old 326 where the run's newest region is 4096 * EVar 334 (LPS c0dd863a: one fresh variable fewer than at 727298f3, as AT_SYSINFO_EHDR's value word is the launch variable [V_EHDR]); with this map both values reach 91 and 94 at counter 368 (recorded 360)). *)
Definition vsh_90_0 : nat -> nat := tshift [(44%nat, 6%nat); (326%nat, 8%nat)].
Definition vsh_90_1 : nat -> nat := tshift [(44%nat, 6%nat); (326%nat, 8%nat)].
Definition startup_plan_seg90_k_0 : plan := psh vsh_90_0 startup_plan_seg90.
Definition startup_plan_seg90_k_1 : plan := psh vsh_90_1 startup_plan_seg90.
Definition startup_plan_seg90_k (r : Z) : plan := if Z.eqb r 1 then startup_plan_seg90_k_1 else startup_plan_seg90_k_0.
Definition seg90_run (r : Z) (s : acs) (T : nat -> option acs) : cres :=
  check ASEGS (mk_itab_ranges ASEGS startup_plan_seg90_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 T 0%nat 400000%nat 3000%nat None s (startup_plan_seg90_k r).
Definition HSC_easan_list_0 : list (nat * acs) := Eval vm_compute in collect_k 6 (seg90_run 0 HS1_easan_90_0) [].
Definition HSC_easan_list_1 : list (nat * acs) := Eval vm_compute in collect_k 6 (seg90_run 1 HS1_easan_90_1) [].
Definition HSC_easan_91_0 : acs := Eval vm_compute in hstate HSC_easan_list_0 HS1_easan_90_0 91.
Definition HSC_easan_94_0 : acs := Eval vm_compute in hstate HSC_easan_list_0 HS1_easan_90_0 94.
Definition HSC_easan_91_1 : acs := Eval vm_compute in hstate HSC_easan_list_1 HS1_easan_90_1 91.
Definition HSC_easan_94_1 : acs := Eval vm_compute in hstate HSC_easan_list_1 HS1_easan_90_1 94.
Definition HSC_easan_table_0 : list (nat * acs) := [(91%nat, HSC_easan_91_0); (94%nat, HSC_easan_94_0)].
Definition HSC_easan_table_1 : list (nat * acs) := [(91%nat, HSC_easan_91_1); (94%nat, HSC_easan_94_1)].
Definition HSC_easan_0 (h : nat) : option acs := hs_lookup h HSC_easan_table_0.
Definition HSC_easan_1 (h : nat) : option acs := hs_lookup h HSC_easan_table_1.
Definition HSC_easan_r (r : Z) : nat -> option acs := if Z.eqb r 1 then HSC_easan_1 else HSC_easan_0.
