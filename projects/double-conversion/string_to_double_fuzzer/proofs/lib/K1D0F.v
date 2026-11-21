(* SPDX-License-Identifier: MIT *)
(* LPS 727298f3: the recorded plan [K1D0.k1s0x] (the main phase's segment into hand-off 105, files
   of 65536 bytes and more) with its [PForget] lists taken by [PlanRegen.fix_forgets]: on each path
   to hand-off 105, a forget index that names, in the state the new run holds there, a fact with
   no variable which the recorded hand-off state [HS_hg1x] carries is left out.  The new run's
   knowledge before the segment's last [PForget] is ordered otherwise than the old run's, so the
   recorded indices named the image pieces KImg 1240009 1240088, KImg 1240392 1240768 and
   KImg 5847892 6373720 (the probe record of this port).  The lists are computed here in the build
   from the certificate's own check; [K1CertS0] checks the plan they give. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanMainDefs MainHSAsan MainItab PlanRegen K0TailAll K1D0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition C_k1s0 : class := (root_class 5 ++ [(QFlen, 65536, QMAX)])%list.
Definition HT_k1s0 : list (nat * (nat * acs)) := [(105%nat, (1%nat, HS_hg1x))].
(* [K1CertS0]'s check, its plan renumbered with its forgets ([PlanRegen.mplan]) *)
Definition k1s0_run (q : plan) : cres :=
  check ASEGS ITm ASAN NX0 AsanInit.LIMIT (XNm ASEGS ASAN NX0 RPN.RP_ASAN (iotab_of C_k1s0)) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of C_k1s0)) (XLm ASEGS ASAN NX0)
        (hs_of HT_k1s0) (lv_of HT_k1s0) TT_r5 KCm BFUELm FUELm None (main_start HS_main 0 C_k1s0) (mplan q).
Definition k1s0x_f : plan := Eval vm_compute in fix_forgets 3000%nat k1s0_run HS_hg1x 105%nat k1s0x.
