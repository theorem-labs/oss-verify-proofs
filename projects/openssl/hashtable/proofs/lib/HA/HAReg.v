(* SPDX-License-Identifier: MIT *)
(* LPS 727298f3: the ASan image's recorded states and plans after the start-up hand-offs, in the new
   numbering and launch layout (double-conversion/string_to_double_fuzzer's MainRegenAsan.v, over
   this unit's states).

   The states and plans after the start-up were recorded against the old start-up run: its numbering
   (NX0 12) and its launch layout.  Each recorded state is [mreg] of the recorded state where the state
   is defined; each recorded plan is renumbered where it is checked ([mplan]).  Before a compaction the
   numbering is the start-up hand-off's, renumbered by [C1HS.C1_F]; after a compaction to [NX0] it is the
   compacted one, renumbered by [K_F] (the compaction base moves from 12 to 15).  The launch facts and
   the four size bounds are computed here in the build from the recorded start-up hand-off state
   ([C1HSRec]) and the one the run reaches ([C1HS.c1_hs0]): [D_OLD] are the recorded state's facts on
   launch variables only that the run does not have, [L_NEW] the run's facts on launch variables only
   that the recorded state does not have.  Nothing here is trusted: each certificate re-runs its check
   on these states and plans. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan PlanRegen C1HSRec C1HS KInv.
Import ListNotations. Import AX2. Import APC. Import CAP.
Open Scope Z_scope.

Definition REC0 : acs := ash C1_F c1_hs0_rec.
Definition D_OLD : list kentry := Eval vm_compute in
  filter (fun K => launch_only NX0 K && negb (kin K (kn c1_hs0))) (kn REC0).
Definition L_NEW : list kentry := Eval vm_compute in
  filter (fun K => launch_only NX0 K && negb (kin K (kn REC0))) (kn c1_hs0).

(* the size bounds' shift: the computed start-up hand-off state's less the recorded one's *)
Definition DT : Z := Eval vm_compute in a_totsz c1_hs0 - a_totsz REC0.
Definition DY : Z := Eval vm_compute in a_ylo c1_hs0 - a_ylo REC0.
Definition DE : Z := Eval vm_compute in a_eager c1_hs0 - a_eager REC0.
Definition DA : Z := Eval vm_compute in a_abytes c1_hs0 - a_abytes REC0.

(* after a compaction: the compacted variables start at NX0 = 15 where they started at 12 *)
Definition K_F : nat -> nat := vshift 12 3.

Definition mreg (S : acs) : acs := resize DT DY DE DA (relaunch NX0 D_OLD L_NEW (ash C1_F S)).
Definition mregk (S : acs) : acs := resize DT DY DE DA (relaunch NX0 D_OLD L_NEW (ash K_F S)).
(* a plan recorded after a compaction, and one recorded before it, which switches at its [PCompact];
   the [D] forms leave out the plan's [PForget] nodes (a certificate checks the plan with them first
   and without them when that fails) *)
Definition mplank (p : plan) : plan := pshs K_F mregk None true p.
Definition mplankD (p : plan) : plan := pshs K_F mregk None false p.
Definition mplan (p : plan) : plan := pshs C1_F mreg (Some mplank) true p.
Definition mplanD (p : plan) : plan := pshs C1_F mreg (Some mplankD) false p.

(* a loop invariant built after a compaction ([KInv.kinv] over a compacted state): its recorded
   facts and descriptor name compacted variables, renumbered by [K_F]; the rest is read off the
   (computed) compacted state *)
Definition kinvk (base : acs) (J : nat) (steps : list (nat * Z)) (hav : list nat) (fd : afd)
    (extra : list kentry) (drop : list nat) : acs :=
  kinv base J steps hav (fdsh K_F fd) (map (ksh K_F) extra) drop.

(* The shared templates the L6 hops hand off to, and the batch data recorded after them, were
   recorded against the old launch layout too.  A VG template names launch variables and its own
   (from 100 up), each of which a hop's signature binds: it keeps its numbering.  A VT template
   shares the variables below its counter with the start it is reached from, in that start's
   numbering ([C1_F]); its batch data names the template's variables and its own from 1130 up (the
   drivers' cell variables and the batch counters, which no start shares; [C1_F] moves the
   template's counter 1120 to 1127).  [V_F] renumbers the first as [C1_F] does and keeps the second.
   Their launch facts and size bounds follow the hops' start states: [HAL6Reg.mregT] (VG) and
   [HAL6Reg.mregV] (VT).  Every batch job re-runs its check on the data so mapped. *)
Definition V_F (v : nat) : nat := if Nat.ltb v 1130 then C1_F v else v.
Definition subV (s : list (nat * expr)) : list (nat * expr) := map (fun q => (V_F (fst q), esh V_F (snd q))) s.
Definition lkV (l : list kentry) : list kentry := map (ksh V_F) l.
