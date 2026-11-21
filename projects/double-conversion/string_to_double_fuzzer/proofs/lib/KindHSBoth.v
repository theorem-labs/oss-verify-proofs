(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: the recorded hand-off state is replaced by the state seg_j1's own check reaches at LPS 727298f3 from both start-up hand-offs, computed in the build. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanMainDefs BothMainDefs.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import MainItabBoth SegJ1Both StartupHSBoth PlanRegen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* LPS 727298f3: as [KindHSAsan], for the ASan+UBSan image *)
Definition seg_j1_both_r : plan := pshf hand_f seg_j1_both.
Definition kind_run_both (h : nat) (hs : nat -> option acs) : cres :=
  check BSEGS BITm BOTHL NX0 AsanInit.LIMIT (XNm BSEGS BOTHL NX0 RPN.RP_BOTH (iotab_of [])) (XEm BSEGS BOTHL NX0) (XBm BSEGS NX0 (iotab_of [])) (BothMainDefs.XLm BSEGS BOTHL NX0)
        hs (fun _ => Some 0%nat) AP.TT_none KCm BFUELm FUELm None (HSA HS_both h) seg_j1_both_r.
Definition HS_kind_both_list : list (nat * acs) :=
  Eval vm_compute in collect_runs (fun _ => 0%nat) 3 [kind_run_both 0; kind_run_both 1] [].

Definition HS_kind_both_0 : acs := match hlookup HS_kind_both_list 0 with Some c => c | None => both_initL end.
Definition HS_kind_both_1 : acs := HS_kind_both_0.   (* [comment removed for export] *)

Definition HS_kind_both (h : nat) : option acs :=
  match h with | 0%nat => Some HS_kind_both_0 | 1%nat => Some HS_kind_both_1 | _ => None end.
