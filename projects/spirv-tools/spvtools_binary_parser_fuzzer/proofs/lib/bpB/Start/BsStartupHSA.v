(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the hand-off states are computed in the build from the start-up plans, one table per CONFIG_RSEQ start state, in place of the recorded states. *)
(* LPS 727298f3: the hand-off states the plans after hand-offs 91 and 94 reach, one table per CONFIG_RSEQ value (from that value's
   states at 91 and 94), computed in the build by [BsStartupRegen.regen] (see there); this file held
   the recorded states of the earlier start-up, which the design-1 start ([BsImages.hinit_r]) no longer reaches. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BxSymExec3 BothPlanCore BothPlan BsHSTab
  BsImages BsPlanImages BsStartupPlan BsStartupRanges BsStartupRegen BsStartupHSC.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition HSA_asan_regen_0 : list (nat * acs) := Eval vm_compute in
  regen 10 [(startup_plan_seg91_xranges, startup_plan_seg91, HSC_asan_91_0);
    (startup_plan_seg94_xranges, startup_plan_seg94, HSC_asan_94_0)].
Definition HSA_asan_regen_1 : list (nat * acs) := Eval vm_compute in
  regen 10 [(startup_plan_seg91_xranges, startup_plan_seg91, HSC_asan_91_1);
    (startup_plan_seg94_xranges, startup_plan_seg94, HSC_asan_94_1)].

Definition HSA_asan_100_0 : acs := Eval vm_compute in hst HSA_asan_regen_0 100.
Definition HSA_asan_101_0 : acs := Eval vm_compute in hst HSA_asan_regen_0 101.
Definition HSA_asan_102_0 : acs := Eval vm_compute in hst HSA_asan_regen_0 102.
Definition HSA_asan_103_0 : acs := Eval vm_compute in hst HSA_asan_regen_0 103.
Definition HSA_asan_104_0 : acs := Eval vm_compute in hst HSA_asan_regen_0 104.
Definition HSA_asan_105_0 : acs := Eval vm_compute in hst HSA_asan_regen_0 105.
Definition HSA_asan_100_1 : acs := Eval vm_compute in hst HSA_asan_regen_1 100.
Definition HSA_asan_101_1 : acs := Eval vm_compute in hst HSA_asan_regen_1 101.
Definition HSA_asan_102_1 : acs := Eval vm_compute in hst HSA_asan_regen_1 102.
Definition HSA_asan_103_1 : acs := Eval vm_compute in hst HSA_asan_regen_1 103.
Definition HSA_asan_104_1 : acs := Eval vm_compute in hst HSA_asan_regen_1 104.
Definition HSA_asan_105_1 : acs := Eval vm_compute in hst HSA_asan_regen_1 105.

Definition HSA_asan_table_0 : list (nat * acs) := [(100%nat, HSA_asan_100_0); (101%nat, HSA_asan_101_0); (102%nat, HSA_asan_102_0); (103%nat, HSA_asan_103_0); (104%nat, HSA_asan_104_0); (105%nat, HSA_asan_105_0)].
Definition HSA_asan_table_1 : list (nat * acs) := [(100%nat, HSA_asan_100_1); (101%nat, HSA_asan_101_1); (102%nat, HSA_asan_102_1); (103%nat, HSA_asan_103_1); (104%nat, HSA_asan_104_1); (105%nat, HSA_asan_105_1)].
Definition HSA_asan_0 (h : nat) : option acs := hs_lookup h HSA_asan_table_0.
Definition HSA_asan_1 (h : nat) : option acs := hs_lookup h HSA_asan_table_1.
Definition HSA_asan_r (r : Z) : nat -> option acs := if Z.eqb r 1 then HSA_asan_1 else HSA_asan_0.
