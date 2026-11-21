(* SPDX-License-Identifier: MIT *)
(* The ASan image's recorded main-phase states in the LPS 727298f3 numbering and launch layout.

   The main phase's plans and states were recorded against the old model's hand-off numbering
   (NX0 10) and launch layout.  Its plans are renumbered where they are checked
   ([PlanRegen.mplan]); each of its recorded states is [mreg] of the recorded state, where the
   state is defined: renumbered by [PlanRegen.hand_f] and [PlanRegen.relaunch]ed.  The two fact
   lists are computed here in the build, from the recorded main hand-off state
   ([MainHSAsanRec]) and the one seg_u's run reaches ([MainHSAsan.HS_main_0]): [D_OLD] are the
   recorded state's facts on launch variables only that the run does not have, [L_NEW] the run's
   facts on launch variables only that the recorded state does not have.  Nothing here is
   trusted: each certificate re-runs the check on these states. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan PlanRegen MainHSAsan.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require MainHSAsanRec.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition REC_main : acs := ash hand_f MainHSAsanRec.HS_main_0.
Definition D_OLD : list kentry :=
  Eval vm_compute in filter (fun K => launch_only NX0 K && negb (kin K (kn HS_main_0))) (kn REC_main).
Definition L_NEW : list kentry :=
  Eval vm_compute in filter (fun K => launch_only NX0 K && negb (kin K (kn REC_main))) (kn HS_main_0).

(* the size bounds' shift: the computed main hand-off state's less the recorded one's *)
Definition DT : Z := a_totsz HS_main_0 - a_totsz REC_main.
Definition DY : Z := a_ylo HS_main_0 - a_ylo REC_main.
Definition DE : Z := a_eager HS_main_0 - a_eager REC_main.
Definition DA : Z := a_abytes HS_main_0 - a_abytes REC_main.

Definition mreg (S : acs) : acs := resize DT DY DE DA (relaunch D_OLD L_NEW (ash hand_f S)).
