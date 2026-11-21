(* SPDX-License-Identifier: MIT *)
(* Made from Reusable/PlanRegen.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), over the twin checker YA0c_w. *)
(* Making the start-up certificates' recorded data in the build rather than by hand, at
   LPS 727298f3 (the method used for jsoncons/fuzz_bigint's start-up data, its PlanRegenK.v).

   WHY: the 727298f3 launch has a longer auxv (27 or 29 pairs by the run's CONFIG_RSEQ
   flag), AT_RANDOM below the strings, and two more launch variables ([V_G], [V_GID]), so
   the states the start-up run hands off, and the one state it joins two arms at, are
   spelled differently from the states recorded against the released model.  A recorded
   state is therefore made again from the run, here, by [check] itself.

   1. [collect_handoffs]: [check]'s [PHandoff h] arm ([YA0c.v]) returns [CErr 4 (PHandoff
   h) cs] when its handoff map has no state for [h], and [CErr 3 (PHandoff h) cs] when the
   reached [cs] does not entail the state it has; [cs] is then the state at that handoff.
   [collect_handoffs] reruns the check: a missing state becomes the reached one, and a state
   some other path does not entail becomes the join of the two.  [collect_handoffs1] makes
   the same map from one run of the check instead of one run per state it adds (below).

   2. [pvia_set]: a plan's [PVia] join state and its fresh-variable floor, replaced where
   the plan is checked, so the recorded plan is not rewritten by hand.

   A state computed this way is a definition, not an assumption: the certificate that names
   it re-runs the check, which must entail it; a wrong state can only make a certificate
   red. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0c YK09 YA01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.BudgetWit.AW Require Import YA0c_w.
Import ListNotations. Import AX2. Import APG.
Open Scope Z_scope.

(* The join of two states that [entails]/[entails_h] must both accept: the knowledge both
   have, the larger fresh counter, and the weaker of each ledger bound those checks compare
   ([a_totsz], [a_eager], [a_abytes] from above, [a_ylo] from below).  Registers, mappings,
   visibility, brk, fd and the tid flag are the first state's; the checks require them
   equal. *)
Definition join_states (a b : acs) : acs :=
let k := filter (fun K => existsb (kentry_eqb K) (kn b)) (kn a) in
let ss := a_ss a in
ACS (mk_ss (s_pc ss) (s_regs ss) k (Nat.max (nxt a) (nxt b))) (a_maps a)
(Z.max (a_totsz a) (a_totsz b)) (Z.min (a_ylo a) (a_ylo b)) (Z.max (a_eager a) (a_eager b))
(a_vis a) (a_ghost a) (Z.max (a_abytes a) (a_abytes b)) (a_brk a) (a_fd a) (a_tidset a).

Definition hlookup (m : list (nat * acs)) (h : nat) : option acs :=
match find (fun q => Nat.eqb (fst q) h) m with Some q => Some (snd q) | None => None end.
Definition hupd (h : nat) (a : acs) (m : list (nat * acs)) : list (nat * acs) :=
(h, a) :: filter (fun q => negb (Nat.eqb (fst q) h)) m.

(* [run m] is the certificate's own check with handoff map [hlookup m]. *)
Fixpoint collect_handoffs (fuel : nat) (run : (nat -> option acs) -> cres) (m : list (nat * acs)) : list (nat * acs) :=
match fuel with
| O => m
| S f =>
match run (hlookup m) with
| CErr code (PHandoff h) cs =>
if Z.eqb code 4 then collect_handoffs f run (hupd h cs m)
else if Z.eqb code 3 then
match hlookup m h with
| Some a => collect_handoffs f run (hupd h (join_states a cs) m)
| None => m
end
else m
| _ => m
end
end.
(* [collect_handoffs1]: the map [collect_handoffs] makes, from ONE run of the check instead of
   one run per state it adds.  [crun] is the certificate's own check written as
   [check_coll] ([YA0c_w.v]) with [hvisit] at its hand-offs, started from [(fuel, m)].
   Why one run gives the same map: [check] reads its map only at [PHandoff h], a leaf, so
   the hand-offs a run reaches, in order, and the state at each, do not depend on the map
   until the run stops at one.  A hand-off a run has passed is passed again by the next run:
   only the state at the [h] just changed is new, and a state that entails [a] entails
   [join_states a b] ([join_states] keeps [a]'s registers, mappings, visibility, brk, fd and
   tid flag, a part of its knowledge, an empty log and weaker ledger bounds).  So
   [collect_handoffs]'s runs make their changes at the hand-offs in the order the run
   reaches them, and [hvisit] makes, at the hand-off reached, the changes they make there,
   one per unit of fuel, until the map entails the reached state; then the run goes on.
   With the fuel spent it changes nothing more, as [collect_handoffs] stops.  The list is
   [collect_handoffs fuel run m]'s, in the same order (computed equal on
   reac-pw/fuzz_headamp's two start-up runs at both CONFIG_RSEQ flags). *)
Fixpoint hvisit_f (b h : nat) (cs : acs) (m : list (nat * acs)) {struct b} : nat * list (nat * acs) :=
match b with
| O => (O, m)
| S b' =>
match hlookup m h with
| None => hvisit_f b' h cs (hupd h cs m)
| Some a => if entails cs a then (b, m) else hvisit_f b' h cs (hupd h (join_states a cs) m)
end
end.
Definition hvisit (h : nat) (cs : acs) (bm : nat * list (nat * acs)) : nat * list (nat * acs) :=
hvisit_f (fst bm) h cs (snd bm).
Definition collect_handoffs1 (fuel : nat) (crun : nat * list (nat * acs) -> cres * (nat * list (nat * acs)))
(m : list (nat * acs)) : list (nat * acs) :=
snd (snd (crun (fuel, m))).
(* the state at handoff [h], or [dflt] when the run never reaches it *)
Definition hstate (m : list (nat * acs)) (dflt : acs) (h : nat) : acs :=
match hlookup m h with Some a => a | None => dflt end.

(* 3. [psh f]: a plan's variable renumbering, as a total function applied where the plan is
   checked, so a recorded plan is not rewritten by hand.  The map is read off the new run (a
   probe that stops the run where the plan names a variable and prints the state), never
   chosen.  WHICH plan fields are variables: the classification of fuzz_bigint's
   jsoncons/fuzz_bigint's [PlanRegenK.v], read from the checker's arms -- PBump
   m, PLoop J, PRename m (both sides), PVia lo; every embedded expr and kentry.  Every other
   nat field stays (registers, list indices, ids, counts).  The embedded states of PLoop and
   PVia are not shifted.  Soundness does not rest on this classification: the certificate
   re-checks the shifted plan, so a wrong map can only make it red. *)
Section Shift.
Variable f : nat -> nat.
Fixpoint esh (e : expr) : expr :=
match e with
| ELit _ => e
| EVar v => EVar (f v)
| EAlu op a b => EAlu op (esh a) (esh b)
| EAluw op a b => EAluw op (esh a) (esh b)
| EMd op a b => EMd op (esh a) (esh b)
| EMdw op a b => EMdw op (esh a) (esh b)
| EExt sx lo n a => EExt sx lo n (esh a)
| EBlob _ _ _ _ => e
end.
Definition sash (a : saddr) : saddr := SA (esh (a_base a)) (a_off a).
Definition ksh (K : kentry) : kentry :=
match K with
| KWord a w v => KWord (sash a) w (esh v)
| KZero a n => KZero (sash a) (esh n)
| KBlob a n k => KBlob (sash a) (esh n) k
| KImg _ _ => K
| KAlign x m => KAlign (esh x) m
| KRange x lo hi => KRange (esh x) lo hi
| KWr a n => KWr (sash a) (esh n)
| KDisj a1 n1 a2 n2 => KDisj (sash a1) (esh n1) (sash a2) (esh n2)
| KFill a n c => KFill (sash a) (esh n) c
| KUnk a n => KUnk (sash a) (esh n)
end.
Definition pesh (p : expr * expr) : expr * expr := (esh (fst p), esh (snd p)).
Fixpoint psh (p : plan) : plan :=
match p with
| PRun stops k => PRun stops (psh k)
| PSplit e mid k1 k2 => PSplit (esh e) mid (psh k1) (psh k2)
| PCase2 e mid k1 k2 => PCase2 (esh e) mid (psh k1) (psh k2)
| PCaseDisj b1 b2 k1 k2 => PCaseDisj (esh b1) (esh b2) (psh k1) (psh k2)
| PShDisj b1 n1 b2 n2 k => PShDisj (esh b1) (esh n1) (esh b2) (esh n2) (psh k)
| PContra => PContra
| PFact K k => PFact (ksh K) (psh k)
| PJoin b off n k => PJoin (esh b) off n (psh k)
| PForget ixs k => PForget ixs (psh k)
| PDropRange b n k => PDropRange (esh b) (esh n) (psh k)
| PGcKeep ws k => PGcKeep (map pesh ws) (psh k)
| PBump m k => PBump (f m) (psh k)
| PHavoc rs k => PHavoc rs (psh k)
| PHavocBig K k => PHavocBig K (psh k)
| PFresh r logc base k => PFresh r logc (option_map esh base) (psh k)
| PSys y k => PSys y (psh k)
| PMmap ka kb => PMmap (psh ka) (psh kb)
| PMmapIn a b c => PMmapIn (psh a) (psh b) (psh c)
| PMprotect a b => PMprotect (psh a) (psh b)
| PBrk2 a b => PBrk2 (psh a) (psh b)
| PX x args k => PX x (map esh args) (psh k)
| PExt id args k => PExt id (map esh args) (psh k)
| PEmit id args k => PEmit id (map esh args) (psh k)
| PExt2 id args k1 k2 => PExt2 id (map esh args) (psh k1) (psh k2)
| PLoop J N inv body k => PLoop (f J) (esh N) inv (psh body) (psh k)
| PNext => PNext
| PHandoff h => PHandoff h
| PExit => PExit
| PSpin => PSpin
| PFog i sz k => PFog i sz (psh k)
| PFogNew i sz k => PFogNew i sz (psh k)
| PGhost b n k => PGhost (esh b) (esh n) (psh k)
| PUnvis b n k => PUnvis (esh b) (esh n) (psh k)
| PHavocBrk lo hi k => PHavocBrk lo hi (psh k)
| PIntro lo hi k => PIntro lo hi (psh k)
| PDiamond joinpc rs k => PDiamond joinpc rs (psh k)
| PRename m k => PRename (map (fun q => (f (fst q), f (snd q))) m) (psh k)
| PCompact k => PCompact (psh k)
| PVia j js lo karms k => PVia j js (f lo) (psh karms) (psh k)
| PMerge j => PMerge j
| PAbstractCell b n k => PAbstractCell (esh b) n (psh k)
| PHavocWords bs k => PHavocWords (map esh bs) (psh k)
| PRespell r e k => PRespell r (esh e) (psh k)
| PMmapInH a b c => PMmapInH (psh a) (psh b) (psh c)
| PMmapIn2 a b => PMmapIn2 (psh a) (psh b)
end.
End Shift.

(* A state [via_ok] refuses (no registers), so a check stops at a [PVia] and returns the
   state there. *)
Definition JS_STOP : acs := ACS (mk_ss 0 [] [] 0) [] 0 0 0 [] [] 0 (ELit 0) FdStd false.

Fixpoint pvia_set (js : acs) (lo : nat) (p : plan) : plan :=
match p with
| PRun stops k => PRun stops (pvia_set js lo k)
| PSplit e mid k1 k2 => PSplit e mid (pvia_set js lo k1) (pvia_set js lo k2)
| PCase2 e mid k1 k2 => PCase2 e mid (pvia_set js lo k1) (pvia_set js lo k2)
| PCaseDisj b1 b2 k1 k2 => PCaseDisj b1 b2 (pvia_set js lo k1) (pvia_set js lo k2)
| PShDisj b1 n1 b2 n2 k => PShDisj b1 n1 b2 n2 (pvia_set js lo k)
| PContra => PContra
| PFact K k => PFact K (pvia_set js lo k)
| PJoin b off n k => PJoin b off n (pvia_set js lo k)
| PForget ixs k => PForget ixs (pvia_set js lo k)
| PDropRange b n k => PDropRange b n (pvia_set js lo k)
| PGcKeep ws k => PGcKeep ws (pvia_set js lo k)
| PBump m k => PBump m (pvia_set js lo k)
| PHavoc rs k => PHavoc rs (pvia_set js lo k)
| PHavocBig K k => PHavocBig K (pvia_set js lo k)
| PFresh r logc base k => PFresh r logc base (pvia_set js lo k)
| PSys y k => PSys y (pvia_set js lo k)
| PMmap ka kb => PMmap (pvia_set js lo ka) (pvia_set js lo kb)
| PMmapIn a b c => PMmapIn (pvia_set js lo a) (pvia_set js lo b) (pvia_set js lo c)
| PMprotect a b => PMprotect (pvia_set js lo a) (pvia_set js lo b)
| PBrk2 a b => PBrk2 (pvia_set js lo a) (pvia_set js lo b)
| PX x args k => PX x args (pvia_set js lo k)
| PExt id args k => PExt id args (pvia_set js lo k)
| PEmit id args k => PEmit id args (pvia_set js lo k)
| PExt2 id args k1 k2 => PExt2 id args (pvia_set js lo k1) (pvia_set js lo k2)
| PLoop J N inv body k => PLoop J N inv (pvia_set js lo body) (pvia_set js lo k)
| PNext => PNext
| PHandoff h => PHandoff h
| PExit => PExit
| PSpin => PSpin
| PFog i sz k => PFog i sz (pvia_set js lo k)
| PFogNew i sz k => PFogNew i sz (pvia_set js lo k)
| PGhost b n k => PGhost b n (pvia_set js lo k)
| PUnvis b n k => PUnvis b n (pvia_set js lo k)
| PHavocBrk l h k => PHavocBrk l h (pvia_set js lo k)
| PIntro l h k => PIntro l h (pvia_set js lo k)
| PDiamond joinpc rs k => PDiamond joinpc rs (pvia_set js lo k)
| PRename m k => PRename m (pvia_set js lo k)
| PCompact k => PCompact (pvia_set js lo k)
| PVia j _ _ karms k => PVia j js lo (pvia_set js lo karms) (pvia_set js lo k)
| PMerge j => PMerge j
| PAbstractCell b n k => PAbstractCell b n (pvia_set js lo k)
| PHavocWords bs k => PHavocWords bs (pvia_set js lo k)
| PRespell r e k => PRespell r e (pvia_set js lo k)
| PMmapInH a b c => PMmapInH (pvia_set js lo a) (pvia_set js lo b) (pvia_set js lo c)
| PMmapIn2 a b => PMmapIn2 (pvia_set js lo a) (pvia_set js lo b)
end.

(* The arms of the first [PVia] of a plan. *)
Fixpoint via_arms (p : plan) : option plan :=
match p with
| PVia _ _ _ karms _ => Some karms
| PRun _ k | PFact _ k | PJoin _ _ _ k | PForget _ k | PDropRange _ _ k | PGcKeep _ k
| PBump _ k | PHavoc _ k | PHavocBig _ k | PFresh _ _ _ k | PSys _ k | PX _ _ k | PExt _ _ k
| PEmit _ _ k | PShDisj _ _ _ _ k | PFog _ _ k | PFogNew _ _ k | PGhost _ _ k | PUnvis _ _ k
| PHavocBrk _ _ k | PIntro _ _ k | PDiamond _ _ k | PRename _ k | PCompact k
| PAbstractCell _ _ k | PHavocWords _ k | PRespell _ _ k => via_arms k
| PSplit _ _ k1 k2 | PCase2 _ _ k1 k2 | PCaseDisj _ _ k1 k2 | PExt2 _ _ k1 k2
| PMmap k1 k2 | PMprotect k1 k2 | PBrk2 k1 k2 | PMmapIn2 k1 k2 =>
match via_arms k1 with Some a => Some a | None => via_arms k2 end
| PMmapIn a b c | PMmapInH a b c =>
match via_arms a with Some x => Some x | None => match via_arms b with Some x => Some x | None => via_arms c end end
| PLoop _ _ _ body k => match via_arms body with Some a => Some a | None => via_arms k end
| _ => None
end.
(* The continuation of the first [PVia] of a plan: what [check] runs from the join state. *)
Fixpoint via_cont (p : plan) : option plan :=
match p with
| PVia _ _ _ _ k => Some k
| PRun _ k | PFact _ k | PJoin _ _ _ k | PForget _ k | PDropRange _ _ k | PGcKeep _ k
| PBump _ k | PHavoc _ k | PHavocBig _ k | PFresh _ _ _ k | PSys _ k | PX _ _ k | PExt _ _ k
| PEmit _ _ k | PShDisj _ _ _ _ k | PFog _ _ k | PFogNew _ _ k | PGhost _ _ k | PUnvis _ _ k
| PHavocBrk _ _ k | PIntro _ _ k | PDiamond _ _ k | PRename _ k | PCompact k
| PAbstractCell _ _ k | PHavocWords _ k | PRespell _ _ k => via_cont k
| PSplit _ _ k1 k2 | PCase2 _ _ k1 k2 | PCaseDisj _ _ k1 k2 | PExt2 _ _ k1 k2
| PMmap k1 k2 | PMprotect k1 k2 | PBrk2 k1 k2 | PMmapIn2 k1 k2 =>
match via_cont k1 with Some a => Some a | None => via_cont k2 end
| PMmapIn a b c | PMmapInH a b c =>
match via_cont a with Some x => Some x | None => match via_cont b with Some x => Some x | None => via_cont c end end
| PLoop _ _ _ body k => match via_cont body with Some a => Some a | None => via_cont k end
| _ => None
end.

(* The state two [PCaseDisj] arms of a [PVia] meet in: each arm is checked from [cs] up to
   its [PMerge] under a join context whose state [PMerge] refuses, which returns the arm's
   end state; the join state is the join of the two.  [chk lc cs p] is the certificate's own
   check from [cs] under loop context [lc]. *)
Definition via_join (chk : option loopctx -> acs -> plan -> cres) (casedisj : acs -> expr -> expr -> option (acs * acs))
(j : nat) (cs : acs) (karms : plan) : option acs :=
match karms with
| PCaseDisj b1 b2 ka kb =>
match casedisj cs b1 b2 with
| Some (csa, csb) =>
let lc := Some (JC j JS_STOP SNil (nxt cs) (nxt cs)) in
match chk lc csa ka, chk lc csb kb with
| CErr _ (PMerge _) ea, CErr _ (PMerge _) eb => Some (join_states ea eb)
| _, _ => None
end
| None => None
end
| _ => None
end.
