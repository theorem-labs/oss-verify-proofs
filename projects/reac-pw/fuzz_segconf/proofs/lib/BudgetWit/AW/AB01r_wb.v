(* Machine-generated data computed from the task's compiled program image (the start-up checker's hand-off states, collected by running the checker over the image); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the 50 hand-off states are fuzz_segconf.asan's own, collected by the start-up collector of tools/startup (the start-up tool set of record, hsform.py 9747a6731b7e) running the donor checker of proofs/cgif/cgif_file_fuzzer on this image with the plan of A/AB05.v probed for it; module paths changed; the comment line above is fuzz_command's (A/AB01.v). *)
(* Modified by Theorem Labs, 2026-11: made from A/AB01.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w); then made for LPS 727298f3 in place of the recorded hand-off states of AB01_w.v and the recorded join state of AB03_w.v: both computed in the build from the start-up run at the 16 GiB limit by check, per CONFIG_RSEQ flag, with BudgetWit/AW/PlanRegen_w.v (as A/AB01r.v), the plan's variables renumbered as in A/AB01r.v; the hand-off states collected in one run of the check; split per CONFIG_RSEQ flag as plugin-hostd/fuzz_command's BudgetWit/AW/AB01r_wb.v, AB01r_w0.v and AB01r_w1.v (the hand-off states collected arm by arm of the continuation's first case split); the shape of reac-pw/fuzz_role's copy. *)
(* The start-up run's hand-off states and its band join state, per value [r] of the run's
   CONFIG_RSEQ flag (0 or 1), computed from the run rather than recorded.  The recorded
   plan [AB05_w.startup_plan_tfib] is checked with its fresh variables renumbered ([vsh]) and
   its one [PVia] join state and floor replaced ([PlanRegen_w.pvia_set]); the recorded
   [AB01_w.HS_tfib] and [AB03_w.JS_tfib_band] were written against the released model's launch. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.reac_pw.fuzz_segconf.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0c YK09 YA01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import YA0c_w YA02_w YA0h_w PlanRegen_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import AB12.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.BudgetWit.AW Require Import AB1h_w AB1l_w AB05_w.
Import ListNotations.
Import AX2. Import APG.
Open Scope Z_scope.

(* the certificate's own check, at flag [r], from state [cs] under loop context [lc] *)
Definition chk_from (r : Z) (HS : nat -> option acs) (lc : option loopctx) (cs : acs) (p : plan) : cres :=
check TSEGS (mk_itab_ranges TSEGS startup_plan_tfib_ranges) TFIB NX0G YA02_w.LIMIT r (XNG TSEGS tfib_XN1) XE0 XB0 HS
(fun _ _ => true) 0%nat 400000%nat 3000%nat lc cs p.
(* the same check run once by [check_coll] (Reusable/YA0c.v), giving each hand-off it reaches
   to PlanRegen's [hvisit], from [bm] (the collector's fuel left and its hand-off map) *)
Definition coll_from (r : Z) (lc : option loopctx) (cs : acs) (p : plan) (bm : nat * list (nat * acs)) : cres * (nat * list (nat * acs)) :=
check_coll TSEGS (mk_itab_ranges TSEGS startup_plan_tfib_ranges) TFIB NX0G YA02_w.LIMIT r (XNG TSEGS tfib_XN1) XE0 XB0
(fun _ _ => true) 0%nat 400000%nat _ hvisit 3000%nat lc cs p bm.
Definition chk (r : Z) (HS : nat -> option acs) (p : plan) : cres :=
chk_from r HS None (init_acs_of_g r TFIB) p.

(* 0. The plan's variables, renumbered to the new run, as this unit's start-up probe reads them on
   the ASan run at the 16 GiB limit at LPS 727298f3 (probe BudgetWit/AW/ZZ_segstartW.v, round
   named in the probe record, markers ZZSEGW_A0..C1; the record is kept outside the tree with the probe
   text).
   - v < 9 keep their numbers and 9 -> 10: the launch layout of Reusable/YA01.v ([V_G] 9, [V_HW] 10,
     [V_GID] 11, NX0G 12), not a probe value.
   - +4 from 10: the recorded plan stops at pc 359696 with the counter at 280, where the plan names
     [EMd M_MUL (ELit 4096) (EVar 275)] and the run's register 10 is [EMd M_MUL (ELit 4096) (EVar 279)],
     at both flags.
   - +6 from 391: with the +4 alone the whole certificate stops at pc 428576 at the plan's [PBump 391]
     (395 under the +4) with the run's counter at 397, at both flags. *)
Definition vsh (v : nat) : nat :=
if Nat.ltb v 9 then v else if Nat.eqb v 9 then 10%nat else if Nat.ltb v 391 then (v + 4)%nat else (v + 6)%nat.
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
(* 3. The plan with that join state, and every hand-off state of the run, collected by
   checking the [PVia]'s continuation from the join state, which is what [check] does
   there. *)
Definition plan_r (js : acs) : plan := pvia_set js (nxt js) plan_sh.
Definition cont : plan := match via_cont plan_sh with Some k => k | None => PContra end.

(* 4. The continuation's first case split ([PSplit (EVar 6) 10], whose second arm is
   [PSplit (EVar 6) 1802]: A/AB05.v [startup_plan_tfib_band20]) and its arms.  Every hand-off
   lies in one of the arms, and no hand-off lies in two ([startup_plan_tfib_s2A3],
   [s2B6], [s2C19] name disjoint hand-offs), so the states [check] reaches at the hand-offs
   are those each arm's own check reaches from the state [check] gives that arm.  Collecting
   them arm by arm costs a run over that arm per step, not a run over the whole continuation:
   [collect_handoffs] reruns its check once per hand-off it adds. *)
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
   [check]'s own [PSplit] arm (Reusable/YA0c.v); a split whose range does not span [mid] has one
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
