(* SPDX-License-Identifier: MIT *)
(* The ASan+UBSan image's recorded main-phase states in the LPS 727298f3 numbering and launch
   layout: [MainRegenAsan]'s rule, from this image's recorded main hand-off state
   ([MainHSBothRec]) and the one its seg_u run reaches ([MainHSBoth.HS_main_both_0]). *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan PlanRegen MainHSBoth.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require MainHSBothRec.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition REC_main_both : acs := ash hand_f MainHSBothRec.HS_main_both_0.
Definition D_OLD_both : list kentry :=
  Eval vm_compute in filter (fun K => launch_only NX0 K && negb (kin K (kn HS_main_both_0))) (kn REC_main_both).
Definition L_NEW_both : list kentry :=
  Eval vm_compute in filter (fun K => launch_only NX0 K && negb (kin K (kn REC_main_both))) (kn HS_main_both_0).

Definition DT_both : Z := a_totsz HS_main_both_0 - a_totsz REC_main_both.
Definition DY_both : Z := a_ylo HS_main_both_0 - a_ylo REC_main_both.
Definition DE_both : Z := a_eager HS_main_both_0 - a_eager REC_main_both.
Definition DA_both : Z := a_abytes HS_main_both_0 - a_abytes REC_main_both.

Definition mreg_both (S : acs) : acs :=
  resize DT_both DY_both DE_both DA_both (relaunch D_OLD_both L_NEW_both (ash hand_f S)).
