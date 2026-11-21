(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the main entry's hand-off states are computed in the build from the start-up plans at both CONFIG_RSEQ values and met into one table, in place of the recorded states. *)
(* LPS 727298f3: the hand-off states the main phase starts from (what the plans after hand-offs 100 .. 105 reach from both CONFIG_RSEQ
   values' states), computed in the build by [BsStartupRegen.regen] (see there) into ONE table, the two values' states at each
   hand-off met by [BsStartupRegen.join_states], so the main phase reads one table; this file held
   the recorded states of the earlier start-up, which the design-1 start ([BsImages.hinit_r]) no longer reaches. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BxSymExec3 BothPlanCore BothPlan BsHSTab
  BsImages BsPlanImages BsStartupPlan BsStartupRanges BsStartupRegen BsStartupHSA.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition HSF_asan_regen : list (nat * acs) := Eval vm_compute in
  regen 10 [(startup_plan_seg100_xranges, startup_plan_seg100, HSA_asan_100_0);
    (startup_plan_seg101_xranges, startup_plan_seg101, HSA_asan_101_0);
    (startup_plan_seg102_xranges, startup_plan_seg102, HSA_asan_102_0);
    (startup_plan_seg103_xranges, startup_plan_seg103, HSA_asan_103_0);
    (startup_plan_seg104_xranges, startup_plan_seg104, HSA_asan_104_0);
    (startup_plan_seg105_xranges, startup_plan_seg105, HSA_asan_105_0);
    (startup_plan_seg100_xranges, startup_plan_seg100, HSA_asan_100_1);
    (startup_plan_seg101_xranges, startup_plan_seg101, HSA_asan_101_1);
    (startup_plan_seg102_xranges, startup_plan_seg102, HSA_asan_102_1);
    (startup_plan_seg103_xranges, startup_plan_seg103, HSA_asan_103_1);
    (startup_plan_seg104_xranges, startup_plan_seg104, HSA_asan_104_1);
    (startup_plan_seg105_xranges, startup_plan_seg105, HSA_asan_105_1)].

Definition HSF_asan_0 : acs := Eval vm_compute in hst HSF_asan_regen 0.
Definition HSF_asan_1 : acs := Eval vm_compute in hst HSF_asan_regen 1.
Definition HSF_asan_2 : acs := Eval vm_compute in hst HSF_asan_regen 2.
Definition HSF_asan_3 : acs := Eval vm_compute in hst HSF_asan_regen 3.
Definition HSF_asan_4 : acs := Eval vm_compute in hst HSF_asan_regen 4.
Definition HSF_asan_5 : acs := Eval vm_compute in hst HSF_asan_regen 5.

Definition HSF_asan_table : list (nat * acs) := [(0%nat, HSF_asan_0); (1%nat, HSF_asan_1); (2%nat, HSF_asan_2); (3%nat, HSF_asan_3); (4%nat, HSF_asan_4); (5%nat, HSF_asan_5)].
Definition HSF_asan (h : nat) : option acs := hs_lookup h HSF_asan_table.
