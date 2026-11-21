(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the hand-off states are computed in the build from the start-up plans, one table per CONFIG_RSEQ start state, in place of the recorded states. *)
(* LPS 727298f3: the hand-off states the plan after hand-off 90 reaches, one table per CONFIG_RSEQ value (from that value's state at 90),
   computed in the build by [BsStartupRegen.regen] (see there); this file held
   the recorded states of the earlier start-up, which the design-1 start ([BsImages.hinit_r]) no longer reaches. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BxSymExec3 BothPlanCore BothPlan BsHSTab
  BsImages BsPlanImages BsStartupPlan BsStartupRanges BsStartupRegen BsStartupHS1.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition HSC_asan_regen_0 : list (nat * acs) := Eval vm_compute in
  regen 10 [(startup_plan_seg90_xranges, startup_plan_seg90, HS1_asan_90_0)].
Definition HSC_asan_regen_1 : list (nat * acs) := Eval vm_compute in
  regen 10 [(startup_plan_seg90_xranges, startup_plan_seg90, HS1_asan_90_1)].

Definition HSC_asan_91_0 : acs := Eval vm_compute in hst HSC_asan_regen_0 91.
Definition HSC_asan_94_0 : acs := Eval vm_compute in hst HSC_asan_regen_0 94.
Definition HSC_asan_91_1 : acs := Eval vm_compute in hst HSC_asan_regen_1 91.
Definition HSC_asan_94_1 : acs := Eval vm_compute in hst HSC_asan_regen_1 94.

Definition HSC_asan_table_0 : list (nat * acs) := [(91%nat, HSC_asan_91_0); (94%nat, HSC_asan_94_0)].
Definition HSC_asan_table_1 : list (nat * acs) := [(91%nat, HSC_asan_91_1); (94%nat, HSC_asan_94_1)].
Definition HSC_asan_0 (h : nat) : option acs := hs_lookup h HSC_asan_table_0.
Definition HSC_asan_1 (h : nat) : option acs := hs_lookup h HSC_asan_table_1.
Definition HSC_asan_r (r : Z) : nat -> option acs := if Z.eqb r 1 then HSC_asan_1 else HSC_asan_0.
