(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: the recorded hand-off state is replaced by the states the start-up plan's own check reaches at LPS 727298f3, one per CONFIG_RSEQ value, computed in the build. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanNodesRP BothPlanImages BothTableL AsanItabFast AsanInit AsanStartup.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import StartupPlanBoth StartupPlanBothR PlanRegen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* LPS 727298f3: as [StartupHSAsan], for the ASan+UBSan image *)
Definition SUB_IT : itab := mk_itab_ranges_fast BSEGS startup_plan_both_ranges.
Definition sub_run (r : Z) (hs : nat -> option acs) : cres :=
  check BSEGS SUB_IT BOTHL NX0 AsanInit.LIMIT (RPN.xn BSEGS BOTHL NX0 RPN.RP_BOTH) XE0 XB0 XL0 hs HL0 AP.TT_none
        0%nat 400000%nat 3000%nat None (both_initL_r r) (startup_plan_both_r r).
Definition HS_both_list : list (nat * acs) :=
  Eval vm_compute in collect_runs (fun h => h) 3 [sub_run 0; sub_run 1] [].

Definition HS_both (h : nat) : option acs := hlookup HS_both_list h.
