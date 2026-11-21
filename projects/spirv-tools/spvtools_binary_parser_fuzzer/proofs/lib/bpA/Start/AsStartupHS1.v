(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the hand-off states are computed in the build from the start-up plans, one table per CONFIG_RSEQ start state, in place of the recorded states. *)
(* LPS 727298f3: the hand-off state the start-up plan reaches, one per CONFIG_RSEQ start state, computed in the build by [AsStartupRegen.regen] (see there); this file held
   the recorded states of the earlier start-up, which the design-1 start ([AsImages.hinit_r]) no longer reaches.  The two values' states
   differ in knowledge (the auxv tail and [V_R]'s value) that the plan after hand-off 90 reads, so each value has its own table. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsHSTab
  AsImages AsPlanImages AsStartupPlan AsStartupRanges AsStartupRegen.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition HS1_asan_regen_0 : list (nat * acs) := Eval vm_compute in
  regen 10 [(startup_plan_xranges, startup_plan, hinit_r 0)].
Definition HS1_asan_regen_1 : list (nat * acs) := Eval vm_compute in
  regen 10 [(startup_plan_xranges, startup_plan, hinit_r 1)].

Definition HS1_asan_90_0 : acs := Eval vm_compute in hst HS1_asan_regen_0 90.
Definition HS1_asan_90_1 : acs := Eval vm_compute in hst HS1_asan_regen_1 90.

Definition HS1_asan_table_0 : list (nat * acs) := [(90%nat, HS1_asan_90_0)].
Definition HS1_asan_table_1 : list (nat * acs) := [(90%nat, HS1_asan_90_1)].
Definition HS1_asan_0 (h : nat) : option acs := hs_lookup h HS1_asan_table_0.
Definition HS1_asan_1 (h : nat) : option acs := hs_lookup h HS1_asan_table_1.
(** the table of a CONFIG_RSEQ value (0 or 1) *)
Definition HS1_asan_r (r : Z) : nat -> option acs := if Z.eqb r 1 then HS1_asan_1 else HS1_asan_0.
