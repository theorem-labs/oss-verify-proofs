(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: the recorded hand-off state is replaced by the state seg_u's own check reaches at LPS 727298f3, computed in the build, keeping the facts PlanRegen.keep_facts keeps against the recorded state (MainHSAsanRec). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanMainDefs.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import MainItab SegAsan KindHSAsan PlanRegen.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require MainHSAsanRec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* LPS 727298f3: [seg_u] in the hand-off numbering, and the state its check reaches at its
   hand-off from [HS_kind 0], computed from the check with an empty hand-off map. *)
Definition seg_u_r : plan := pshf hand_f seg_u.
Definition main_run (hs : nat -> option acs) : cres :=
  check ASEGS ITm ASAN NX0 AsanInit.LIMIT (XNm ASEGS ASAN NX0 RPN.RP_ASAN (iotab_of [])) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of [])) (XLm ASEGS ASAN NX0)
        hs (fun _ => Some 0%nat) AP.TT_none KCm BFUELm FUELm None (HSA HS_kind 0) seg_u_r.
Definition HS_main_run : acs :=
  Eval vm_compute in match hlookup (collect_handoffs 20 main_run []) 0 with Some c => c | None => asan_init end.
(* the run's own state, its knowledge chosen by [keep_facts] against the recorded state renumbered *)
Definition HS_main_0 : acs := Eval vm_compute in keep_facts NX0 (ash hand_f MainHSAsanRec.HS_main_0) HS_main_run.
Definition HS_main_1 : acs := HS_main_0.   (* [comment removed for export] *)

Definition HS_main (h : nat) : option acs :=
  match h with | 0%nat => Some HS_main_0 | 1%nat => Some HS_main_1 | _ => None end.
