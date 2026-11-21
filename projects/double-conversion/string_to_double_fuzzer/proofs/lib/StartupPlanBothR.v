(* SPDX-License-Identifier: MIT *)
(* LPS 727298f3: the ASan+UBSan twin of [StartupPlanAsanR]: the recorded
   start-up plan of [StartupPlanBoth], renumbered where it is checked, by the same rules (the
   twin's plan names the same fresh-variable literals and has the same AT_RANDOM node, hand-off
   compaction and munmap; the probe record names the twin's own probe values). *)
From Stdlib Require Import ZArith List.
From Corelib Require Import PrimString.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanStateCodec AsanPlanCodec StartupPlanBoth PlanRegen StartupPlanAsanR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition memk1_both_r (h : nat) : plan :=
  match startup_plan_both_memk1 with
  | PRun s1 (PX x a (PRun s2 (PHavocWords ws (PAbstractCell b n (PJoinV b' _ m k))))) =>
      PRun s1 (PX x a (PRun s2 (PHavocWords ws (PAbstractCell b n (PJoinV b' (snd e_atrb + 8) m (su_tail h k))))))
  | _ => PContra
  end.

Definition startup_plan_both_s : string :=
  ltac:(lazymatch eval cbv delta [startup_plan_both] in startup_plan_both with dec_plan _ ?s => exact s end).
Definition sub_holes (h : nat) (t : nat) : option plan := if Nat.eqb t HOLE_MEMK1 then Some (memk1_both_r h) else None.

(* the plan at CONFIG_RSEQ value [r] (0 or 1) *)
Definition startup_plan_both_r (r : Z) : plan :=
  psh su_f (sub_holes (Z.to_nat r)) (Some su_kref) (ash su_f) true
    (dec_plan (PE [startup_plan_both_tospin2; PTail HOLE_MEMK1] [] [e_stklo; e_stkn] [] [] []) startup_plan_both_s).
