(* SPDX-License-Identifier: MIT *)
(* LPS 727298f3: the ASan+UBSan twin of [K1D0F]: the recorded plan [K1BD0.k1s0x] with its
   [PForget] lists taken by [PlanRegen.fix_forgets] against [K1BD0.HS_hg1x], computed here in the
   build from [K1BCertS0]'s own check. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanMainDefs BothMainDefs MainHSBoth MainItabBoth PlanRegen BK0TailAll K1BD0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition C_k1s0 : class := (root_class 5 ++ [(QFlen, 65536, QMAX)])%list.
Definition HT_k1s0 : list (nat * (nat * acs)) := [(105%nat, (1%nat, HS_hg1x))].
(* [K1BCertS0]'s check, its plan renumbered with its forgets ([PlanRegen.mplan]) *)
Definition k1s0_run (q : plan) : cres :=
  check BSEGS BITm BOTHL NX0 AsanInit.LIMIT (XNm BSEGS BOTHL NX0 RPN.RP_BOTH (iotab_of C_k1s0)) (XEm BSEGS BOTHL NX0) (XBm BSEGS NX0 (iotab_of C_k1s0)) (BothMainDefs.XLm BSEGS BOTHL NX0)
        (hs_of HT_k1s0) (lv_of HT_k1s0) TT_r5 KCm BFUELm FUELm None (main_start HS_main_both 0 C_k1s0) (mplan q).
Definition k1s0x_f : plan := Eval vm_compute in fix_forgets 3000%nat k1s0_run HS_hg1x 105%nat k1s0x.
