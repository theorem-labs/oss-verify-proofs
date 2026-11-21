(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: the recorded hand-off state is replaced by the state seg_u's own check reaches at LPS 727298f3, computed in the build, keeping the facts PlanRegen.keep_facts keeps against the recorded state (MainHSBothRec). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanMainDefs BothMainDefs.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import MainItabBoth SegBoth KindHSBoth PlanRegen.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require MainHSBothRec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* LPS 727298f3: as [MainHSAsan], for the ASan+UBSan image *)
Definition seg_u_both_r : plan := pshf hand_f seg_u_both.
Definition main_run_both (hs : nat -> option acs) : cres :=
  check BSEGS BITm BOTHL NX0 AsanInit.LIMIT (XNm BSEGS BOTHL NX0 RPN.RP_BOTH (iotab_of [])) (XEm BSEGS BOTHL NX0) (XBm BSEGS NX0 (iotab_of [])) (BothMainDefs.XLm BSEGS BOTHL NX0)
        hs (fun _ => Some 0%nat) AP.TT_none KCm BFUELm FUELm None (HSA HS_kind_both 0) seg_u_both_r.
Definition HS_main_both_run : acs :=
  Eval vm_compute in match hlookup (collect_handoffs 20 main_run_both []) 0 with Some c => c | None => both_initL end.
Definition HS_main_both_0 : acs := Eval vm_compute in keep_facts NX0 (ash hand_f MainHSBothRec.HS_main_both_0) HS_main_both_run.
Definition HS_main_both_1 : acs := HS_main_both_0.   (* [comment removed for export] *)

Definition HS_main_both (h : nat) : option acs :=
  match h with | 0%nat => Some HS_main_both_0 | 1%nat => Some HS_main_both_1 | _ => None end.
