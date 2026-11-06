(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore BsStartupPlan BothPlanImages.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init5Logic02eq79OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsanPlanCore3APC~~~~~~h8emk_itab_ranges79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~mc4itab69OSSVerify6Proofsaboost_jsonafuzz_parse3libeBothPlanImages~~~~~~r45ASEGS69OSSVerify6Proofsaboost_jsonafuzz_parse3libdBsStartupItab~~~~~~vd8ARM_ITAB69OSSVerify6Proofsaboost_jsonafuzz_parse3libdBsStartupPlan~~~~~~hk8hbstartup_plan_seg100_xranges" s.
Import ListNotations. Import AX2. Import APC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition ARM_ITAB : itab := Eval vm_compute in (mk_itab_ranges ASEGS startup_plan_seg100_xranges).
Lemma ARM_ITAB_eq : ltac2:(zQ "60!h4!lb!qd!v5!hjd!ho8@3$0$2$4@2$1$3$5").
Proof. vm_cast_no_check (@eq_refl itab ARM_ITAB). Qed.
