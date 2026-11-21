(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 in place of the recorded hand-off states of AB01.v and the recorded join state of AB03.v, from libreac/fuzz_boxreg's A/AB01r.v: the definitions of their computation in the build from the start-up run by check, per CONFIG_RSEQ flag, with Reusable/PlanRegen.v, the plan's fresh variables renumbered by a map read from this unit's probes, and the arms of the plan's first case split after the band join, so that A/AB01r0.v and A/AB01r1.v collect the hand-off states of each arm, one file per flag (the layout of plugin-hostd/fuzz_command's A/AB01rb.v), the hand-off states collected in one run of the check (the collector of reac-pw/fuzz_headamp's Reusable/PlanRegen.v and Reusable/YA0c.v). *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 at the 16 GiB limit (lib/BudgetWit/AW, the modules it imports from that set renamed to their twins, suffix _w) in place of the recorded hand-off states of AB01_w.v and the recorded join state of AB03_w.v, from this unit's A/AB01r.v (itself made in the shape of libreac/fuzz_boxreg's A/AB01r.v): the definitions of their computation in the build from the start-up run by check, per CONFIG_RSEQ flag, with BudgetWit/AW/PlanRegen_w.v, the plan's fresh variables renumbered by a map read from this unit's probes, and the arms of the plan's first case split after the band join, so that BudgetWit/AW/AB01r0_w.v and BudgetWit/AW/AB01r1_w.v collect the hand-off states of each arm, one file per flag (the layout of plugin-hostd/fuzz_command's A/AB01rb.v), the hand-off states collected in one run of the check (the collector of reac-pw/fuzz_headamp's Reusable/PlanRegen.v and Reusable/YA0c.v); taken from projects/libreac/fuzz_pcap/proofs/lib/A/AB01rb.v, lines 10-15 and 19-180, as in the LPS 727298f3 update. *)
(* The start-up run's hand-off states and its band join state, per value [r] of the run's
   CONFIG_RSEQ flag (0 or 1), computed from the run rather than recorded.  The recorded
   plan [AB05_w.startup_plan_tfib] is checked with its fresh variables renumbered ([vsh]) and
   its one [PVia] join state and floor replaced ([PlanRegen_w.pvia_set]); the recorded
   [AB01_w.HS_tfib] and [AB03_w.JS_tfib_band] were written against the released model's launch. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.libreac.fuzz_pcap.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0c YK09 YA01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB12.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.

(* the certificate's own check, at flag [r], from state [cs] under loop context [lc] *)
Definition chk_from (r : Z) (HS : nat -> option acs) (lc : option loopctx) (cs : acs) (p : plan) : cres :=
check TSEGS (mk_itab_ranges TSEGS startup_plan_tfib_ranges) TFIB NX0G YA02_w.LIMIT r (XNG TSEGS tfib_XN1) XE0 XB0 HS
(fun _ _ => true) 0%nat 400000%nat 3000%nat lc cs p.
(* the same check run once by [check_coll] (BudgetWit/AW/YA0c_w.v), giving each hand-off it reaches
   to PlanRegen_w's [hvisit], from [bm] (the collector's fuel left and its hand-off map) *)
Definition coll_from (r : Z) (lc : option loopctx) (cs : acs) (p : plan) (bm : nat * list (nat * acs)) : cres * (nat * list (nat * acs)) :=
check_coll TSEGS (mk_itab_ranges TSEGS startup_plan_tfib_ranges) TFIB NX0G YA02_w.LIMIT r (XNG TSEGS tfib_XN1) XE0 XB0
(fun _ _ => true) 0%nat 400000%nat _ hvisit 3000%nat lc cs p bm.
Definition chk (r : Z) (HS : nat -> option acs) (p : plan) : cres :=
chk_from r HS None (init_acs_of_g r TFIB) p.

(* 0. The plan's variables, renumbered to the new run at the 16 GiB limit.  [AB05_w] is
   [AB05]'s plan text (only its imports differ).  Read on this run from this unit's probe
   BudgetWit/AW/ZZ_pcstartW.v (notes/probe-libreac__fuzz_pcap.md), as A/AB01r.v's map is read on the
   8 GiB run: v < 9 the same and 9 -> 10 from the launch layout of Reusable/YA01.v; with the join
   state refused, the unshifted run reaches the plan's [PVia] at counter 280 with register 10
   holding [4096 * EVar 279] (markers ZZPCW_U0 and ZZPCW_U1, both flags): four higher from 10;
   with the four-shift alone, the check from the computed join state stops at [PBump 395] with
   the counter at 397 (ZZPCW_V4_0 and ZZPCW_V4_1): six higher from 391.  Under [vsh] the check
   ends [COk] at both flags with the recorded shape (ZZPCW_C0, ZZPCW_C1).  Read, not chosen. *)
Definition vsh (v : nat) : nat :=
if Nat.ltb v 9 then v else if Nat.eqb v 9 then 10%nat
else if Nat.ltb v 391 then (v + 4)%nat else (v + 6)%nat.
Definition plan_sh : plan := psh vsh startup_plan_tfib.
(* 1. The plan with its join state refused: the run up to the [PVia] and the state there. *)
Definition plan_stop : plan := pvia_set JS_STOP 0 plan_sh.
Definition cs_via (r : Z) : acs :=
match chk r (fun _ => None) plan_stop with CErr _ (PVia _ _ _ _ _) cs => cs | _ => JS_STOP end.
(* 2. The join state: the join of the two arms' end states; its floor is its own counter. *)
Definition js_of (r : Z) (cs : acs) : acs :=
match via_arms plan_sh with
| Some karms =>
match via_join (fun lc c p => chk_from r (fun _ => None) lc c p) node_casedisj_g 1 cs karms with
| Some js => js
| None => JS_STOP
end
| None => JS_STOP
end.
(* 3. The plan with that join state; the [PVia]'s continuation, which [check] runs from the
   join state. *)
Definition plan_r (js : acs) : plan := pvia_set js (nxt js) plan_sh.
Definition cont : plan := match via_cont plan_sh with Some k => k | None => PContra end.

(* 4. The continuation's first case split ([PSplit (EVar 6) 10], whose second arm is
   [PSplit (EVar 6) 1802]: BudgetWit/AW/AB05_w.v [startup_plan_tfib_band20]) and its arms.  Every hand-off
   lies in one of the arms, and no hand-off lies in two ([startup_plan_tfib_s2A3],
   [s2B6], [s2C19] name disjoint hand-offs), so the states [check] reaches at the hand-offs
   are those each arm's own check reaches from the state [check] gives that arm.  Collecting
   them arm by arm costs a run over that arm, not a run over the whole continuation; each arm's
   hand-offs are collected in one run of the check ([collect_handoffs1] over [coll_from]). *)
(* The continuation with its case splits refused: [check] stops at the first one with code 4
   at hand-off [SPLIT_STOP], which no plan names, and returns the state there. *)
Definition SPLIT_STOP : nat := 999%nat.
Fixpoint split_cut (p : plan) : plan :=
match p with
| PRun stops k => PRun stops (split_cut k)
| PSplit _ _ _ _ => PHandoff SPLIT_STOP
| PCase2 e mid k1 k2 => PCase2 e mid (split_cut k1) (split_cut k2)
| PCaseDisj b1 b2 k1 k2 => PCaseDisj b1 b2 (split_cut k1) (split_cut k2)
| PShDisj b1 n1 b2 n2 k => PShDisj b1 n1 b2 n2 (split_cut k)
| PContra => PContra
| PFact K k => PFact K (split_cut k)
| PJoin b off n k => PJoin b off n (split_cut k)
| PForget ixs k => PForget ixs (split_cut k)
| PDropRange b n k => PDropRange b n (split_cut k)
| PGcKeep ws k => PGcKeep ws (split_cut k)
| PBump m k => PBump m (split_cut k)
| PHavoc rs k => PHavoc rs (split_cut k)
| PHavocBig K k => PHavocBig K (split_cut k)
| PFresh r logc base k => PFresh r logc base (split_cut k)
| PSys y k => PSys y (split_cut k)
| PMmap ka kb => PMmap (split_cut ka) (split_cut kb)
| PMmapIn a b c => PMmapIn (split_cut a) (split_cut b) (split_cut c)
| PMprotect a b => PMprotect (split_cut a) (split_cut b)
| PBrk2 a b => PBrk2 (split_cut a) (split_cut b)
| PX x args k => PX x args (split_cut k)
| PExt id args k => PExt id args (split_cut k)
| PEmit id args k => PEmit id args (split_cut k)
| PExt2 id args k1 k2 => PExt2 id args (split_cut k1) (split_cut k2)
| PLoop J N inv body k => PLoop J N inv (split_cut body) (split_cut k)
| PNext => PNext
| PHandoff h => PHandoff h
| PExit => PExit
| PSpin => PSpin
| PFog i sz k => PFog i sz (split_cut k)
| PFogNew i sz k => PFogNew i sz (split_cut k)
| PGhost b n k => PGhost b n (split_cut k)
| PUnvis b n k => PUnvis b n (split_cut k)
| PHavocBrk l h k => PHavocBrk l h (split_cut k)
| PIntro l h k => PIntro l h (split_cut k)
| PDiamond joinpc rs k => PDiamond joinpc rs (split_cut k)
| PRename m k => PRename m (split_cut k)
| PCompact k => PCompact (split_cut k)
| PVia j js lo karms k => PVia j js lo (split_cut karms) (split_cut k)
| PMerge j => PMerge j
| PAbstractCell b n k => PAbstractCell b n (split_cut k)
| PHavocWords bs k => PHavocWords bs (split_cut k)
| PRespell r e k => PRespell r e (split_cut k)
| PMmapInH a b c => PMmapInH (split_cut a) (split_cut b) (split_cut c)
| PMmapIn2 a b => PMmapIn2 (split_cut a) (split_cut b)
end.
(* The first case split of a plan, in [via_cont]'s order. *)
Fixpoint split_node (p : plan) : option plan :=
match p with
| PSplit _ _ _ _ => Some p
| PRun _ k | PFact _ k | PJoin _ _ _ k | PForget _ k | PDropRange _ _ k | PGcKeep _ k
| PBump _ k | PHavoc _ k | PHavocBig _ k | PFresh _ _ _ k | PSys _ k | PX _ _ k | PExt _ _ k
| PEmit _ _ k | PShDisj _ _ _ _ k | PFog _ _ k | PFogNew _ _ k | PGhost _ _ k | PUnvis _ _ k
| PHavocBrk _ _ k | PIntro _ _ k | PDiamond _ _ k | PRename _ k | PCompact k
| PAbstractCell _ _ k | PHavocWords _ k | PRespell _ _ k => split_node k
| PCase2 _ _ k1 k2 | PCaseDisj _ _ k1 k2 | PExt2 _ _ k1 k2
| PMmap k1 k2 | PMprotect k1 k2 | PBrk2 k1 k2 | PMmapIn2 k1 k2 =>
match split_node k1 with Some a => Some a | None => split_node k2 end
| PMmapIn a b c | PMmapInH a b c =>
match split_node a with Some x => Some x | None => match split_node b with Some x => Some x | None => split_node c end end
| PLoop _ _ _ body k => match split_node body with Some a => Some a | None => split_node k end
| PVia _ _ _ karms k => match split_node karms with Some a => Some a | None => split_node k end
| _ => None
end.
(* The state at the first case split of the continuation, from the join state [js]. *)
Definition cs_split (r : Z) (js : acs) : acs :=
match chk_from r (fun _ => None) None js (split_cut cont) with
| CErr c (PHandoff h) cs => if (Z.eqb c 4 && Nat.eqb h SPLIT_STOP)%bool then cs else JS_STOP
| _ => JS_STOP
end.
(* The arms of nested case splits and the state [check] gives each: the arm of
   [PSplit e mid k1 k2] whose range spans [mid] gets the range fact of its side, word for word
   [check]'s own [PSplit] arm (BudgetWit/AW/YA0c_w.v); a split whose range does not span [mid] has one
   arm, with the state unchanged. *)
Fixpoint split_arms (d : nat) (cs : acs) (p : plan) : list (acs * plan) :=
match d with
| O => [(cs, p)]
| S d' =>
match p with
| PSplit e mid k1 k2 =>
if expr_vars_lt NX0G e then
match erange (kn cs) e with
| Some (lo, hi) =>
if (Z.leb lo mid && Z.ltb mid hi)%bool then
split_arms d' (set_kn cs (KRange e lo mid :: kn cs)) k1 ++ split_arms d' (set_kn cs (KRange e (mid + 1) hi :: kn cs)) k2
else if Z.leb hi mid then split_arms d' cs k1 else split_arms d' cs k2
| None => []
end
else []
| _ => [(cs, p)]
end
end.
(* Every hand-off state the run reaches after the join, at flag [r] from join state [js]:
   [collect_handoffs] over each arm of the first case split, from the state [check] gives it. *)
Definition HSL_arms (r : Z) (js : acs) : list (nat * acs) :=
match split_node cont with
| Some sp =>
flat_map (fun ap => collect_handoffs1 60 (coll_from r None (fst ap) (snd ap)) [])
  (split_arms 4 (cs_split r js) sp)
| None => []
end.
