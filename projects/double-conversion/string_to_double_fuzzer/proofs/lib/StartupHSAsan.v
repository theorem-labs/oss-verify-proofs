(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: the recorded hand-off state is replaced by the states the start-up plan's own check reaches at LPS 727298f3, one per CONFIG_RSEQ value, computed in the build. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanNodesRP AsanPlanImages AsanItabFast AsanInit AsanStartup.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import StartupPlanAsan StartupPlanAsanR PlanRegen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* LPS 727298f3 (the method of jsoncons/fuzz_bigint's PlanRegenK.v): the hand-off
   states are computed from the start-up plan's own check with an empty hand-off map (the state
   each CONFIG_RSEQ value's run reaches at its hand-off), never recorded.  The certificate
   [AsanStartupCert.startup_cert] re-runs the check against them. *)
Definition SU_IT : itab := mk_itab_ranges_fast ASEGS startup_plan_ranges.
Definition su_run (r : Z) (hs : nat -> option acs) : cres :=
  check ASEGS SU_IT ASAN NX0 AsanInit.LIMIT (RPN.xn ASEGS ASAN NX0 RPN.RP_ASAN) XE0 XB0 XL0 hs HL0 AP.TT_none
        0%nat 400000%nat 3000%nat None (asan_init_r r) (startup_plan_r r).
Definition HS_asan_list : list (nat * acs) :=
  Eval vm_compute in collect_runs (fun h => h) 3 [su_run 0; su_run 1] [].

Definition HS_asan (h : nat) : option acs := hlookup HS_asan_list h.
