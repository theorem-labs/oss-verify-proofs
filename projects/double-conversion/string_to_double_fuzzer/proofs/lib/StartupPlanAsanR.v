(* SPDX-License-Identifier: MIT *)
(* LPS 727298f3 (the method of jsoncons/fuzz_bigint's PlanRegenK.v): the recorded
   start-up plan of [StartupPlanAsan], renumbered where it is checked.  Nothing recorded is edited:
   the run's fresh-variable literals move by a total monotone map read from probe runs, the
   hand-off compaction's targets move to the hand-off numbering ([PlanRegen.hand_f]), the one
   recorded node that names the launch layout by a literal offset is rebuilt from the layout's
   own expression, and the munmap's refused child is the node the probe run reads.  The probe
   record of this port names each run and the
   output line each value comes from. *)
From Stdlib Require Import ZArith List.
From Corelib Require Import PrimString.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanStateCodec AsanPlanCodec StartupPlanAsan PlanRegen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* The run's map, old numbering -> new: the lowest fresh variable the recorded plan names is the
   old 43, which the new run holds as 48; every one up to the old 333 moves by 5, and from the
   old 334 on by 7 (the launch has three more plan variables and the auxv walk reads the whole
   vector).  The live variables at the hand-off compaction are exactly the compaction's sources
   under this map. *)
Definition SU_TBL : list (nat * nat) := [(43, 5); (334, 7)]%nat.
Definition su_f : nat -> nat := tshift SU_TBL.

(* [startup_plan_memk1] names AT_RANDOM through [e_atrandom]/[e_atrb], whose terms are the launch
   variables [V_G]/[V_R] of the NEW numbering, so it is not renumbered as a whole.  Its
   [PJoinV (fst e_atrb) 192 8] is the word 8 bytes into the AT_RANDOM block: 192 is the old
   layout's [snd e_atrb] (184 = 16 + 8 + 160) plus 8, so here the offset is [snd e_atrb + 8].
   Its tail is the hand-off compaction: run variables (by [su_f]) to hand-off ones (by [hand_f]).
   One chain per CONFIG_RSEQ value [r]: the run at [r] hands off at [r] (the two states differ in
   the auxv pairs from 26 on, which musl's auxv walks read after the hand-off). *)
Definition su_tail (h : nat) (p : plan) : plan :=
  match p with
  | PRename m (PBump b (PHandoff _)) => PRename (map (fun q => (su_f (fst q), hand_f (snd q))) m) (PBump (hand_f b) (PHandoff h))
  | _ => PContra
  end.
Definition memk1_r (h : nat) : plan :=
  match startup_plan_memk1 with
  | PRun s1 (PX x a (PRun s2 (PHavocWords ws (PAbstractCell b n (PJoinV b' _ m k))))) =>
      PRun s1 (PX x a (PRun s2 (PHavocWords ws (PAbstractCell b n (PJoinV b' (snd e_atrb + 8) m (su_tail h k))))))
  | _ => PContra
  end.

(* the recorded plan's own text, and its other sub-plan *)
Definition startup_plan_s : string :=
  ltac:(lazymatch eval cbv delta [startup_plan] in startup_plan with dec_plan _ ?s => exact s end).
Definition HOLE_MEMK1 : nat := 1000.
Definition su_holes (h : nat) (t : nat) : option plan := if Nat.eqb t HOLE_MEMK1 then Some (memk1_r h) else None.

(* The munmap at pc 557684 (sanitizer_common's [UnmapOrDie] of a one-page buffer) can be refused
   at LPS 727298f3.  The refused child takes [internal_iserror]'s error branch to
   [ReportMunmapFailureAndDie] and reaches pc 539540 with no system call on the way, where the
   run spins: its plan is [PRun [] PSpin]. *)
Definition su_kref : plan := PRun [] PSpin.

(* the plan at CONFIG_RSEQ value [r] (0 or 1) *)
Definition startup_plan_r (r : Z) : plan :=
  psh su_f (su_holes (Z.to_nat r)) (Some su_kref) (ash su_f) true
    (dec_plan (PE [startup_plan_tospin2; PTail HOLE_MEMK1] [] [e_stklo; e_stkn] [] [] []) startup_plan_s).
