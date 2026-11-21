(* SPDX-License-Identifier: MIT *)
(* Made from projects/cjson/cjson_read_fuzzer/proofs/lib/AS/PlanRegen.v (itself made from
   projects/jsoncons/fuzz_bigint/proofs/lib/PlanRegenK.v and
   projects/double-conversion/string_to_double_fuzzer/proofs/lib/PlanRegen.v) and the join
   collector of projects/skcms/iccprofile_info/proofs/lib/Asan/PlanRegen.v, over this unit's plan
   and state types: the LPS 727298f3 start-up certificate data computed in the build.

   1. [psh f]: a plan's variable renumbering, a total function applied where the plan is checked,
   so a recorded plan is not rewritten by hand.  LPS 727298f3 gives the launch one more plan
   variable ([V_GID] = 12, the old [NX0]; NX0 12 -> 13) and more of the auxv to read, so the runs
   allocate their fresh variables at other numbers than the runs the recorded plans were written
   against.  Each map is read off the new run (a probe that stops the run where the plan names a
   variable and prints the state), never chosen.

   WHICH plan fields are variables: read from [AsanPlan.check]'s arms -- PBump m, PLoop J,
   PRename m (both sides), PVia lo; every embedded expr and kentry.  Every other nat field stays:
   registers (PHavoc, PFresh, PDiamond, PRespell), list indices (PForget, PFog, PFogNew), ids
   (PExt, PEmit, PExt2, PHandoff, PMerge, PVia j), counts (PJoin, PHavocBig).  The states written
   inside PLoop and PVia are left alone by [psh]; [pjs] puts the computed join states in.
   SOUNDNESS DOES NOT REST ON THIS CLASSIFICATION: the certificates vm_compute through [psh] and
   [pjs] and re-check the resulting plan; a wrong map or classification can only make a
   certificate fail.

   2. [collect_hjf1]: the hand-off states and join states of a run, computed from one run of the
   check ([AsanPlan.check_coll]).
   [check]'s [PHandoff h] arm returns [CErr 4 (PHandoff h) cs] when its hand-off map has no state
   for [h] and [CErr 3 (PHandoff h) cs] when the reached [cs] does not entail the state it has;
   its [PMerge j] arm returns [CErr 3 (PMerge j) cs] when an arm's state [cs] does not entail the
   join state.  A state computed this way is a definition, not an assumption: the certificate that
   names it re-runs the check, which must entail it.

   3. [filt_rec]: the fixed rule of the run record ('Hand-off states filtered by a fixed rule', with
   double-conversion's refinement for variable-free facts) for a computed state: keep a fact that
   names a launch variable (below [nx0]) and no fresh one, and any other fact (one on a fresh
   variable, or one that names no variable) only if the recorded state, renumbered by the
   probe-read map, names it too.  Every kept fact is the run's own; dropping facts only weakens the
   state, and the certificate still checks every entailment. *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import AP.

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
    | PMmap k => PMmap (psh k)
    | PMmapIn k => PMmapIn (psh k)
    | PMprotect k => PMprotect (psh k)
    | PBrk2 a b => PBrk2 (psh a) (psh b)
    | PX x args k => PX x (map esh args) (psh k)
    | PExt id args k => PExt id (map esh args) (psh k)
    | PEmit id args k => PEmit id (map esh args) (psh k)
    | PExt2 id args k1 k2 => PExt2 id (map esh args) (psh k1) (psh k2)
    | PLoop J N inv body k => PLoop (f J) (esh N) inv (psh body) (psh k)
    | PNext => PNext
    | PHandoff h => PHandoff h
    | PExit => PExit
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
    end.

  (* a shape names the split expressions of the run it records *)
  Fixpoint shsh (s : shape) : shape :=
    match s with
    | SCase e mid a b => SCase (esh e) mid (shsh a) (shsh b)
    | SAlt2 a b => SAlt2 (shsh a) (shsh b)
    | SEmitP fd ps a => SEmitP fd ps (shsh a)
    | _ => s
    end.
End Shift.

(* A total increasing map given as a table read from probes: ascending thresholds [(t, d)] in
   the OLD numbering; an old variable [v] moves by the [d] of the last [t <= v], and by 0 below
   the first threshold. *)
Fixpoint tbl_d (tbl : list (nat * nat)) (v acc : nat) : nat :=
  match tbl with [] => acc | (t, d) :: r => if Nat.leb t v then tbl_d r v d else acc end.
Definition tshift (tbl : list (nat * nat)) (v : nat) : nat := (v + tbl_d tbl v 0)%nat.

(* The join of two states.  [AsanPlanCore.entails] needs equal registers, mappings, visibility,
   ghosts, brk, fd and tid flag, a subset of the knowledge, and bounds on four sizes; so the join
   is the first state with the knowledge both have and the four sizes at their weaker ends.  At a
   [PMerge] ([entails_h]) the registers of the join state that name a variable at or above the
   via's [lo] are matched by any expression, so the first state's registers serve there too. *)
Definition join_states (a b : acs) : acs :=
  let ss := a_ss a in
  ACS (SSR (s_pc ss) (s_regs ss) (s_log ss) (filter (fun K => existsb (kentry_eqb K) (kn b)) (kn a))
           (Nat.max (nxt a) (nxt b)) (s_resv ss))
      (a_maps a) (Z.max (a_totsz a) (a_totsz b)) (Z.min (a_ylo a) (a_ylo b))
      (Z.max (a_eager a) (a_eager b)) (a_vis a) (a_ghost a) (Z.max (a_abytes a) (a_abytes b))
      (a_brk a) (a_fd a) (a_tidset a).

Definition hlookup (m : list (nat * acs)) (h : nat) : option acs :=
  match find (fun q => Nat.eqb (fst q) h) m with Some q => Some (snd q) | None => None end.
Definition hupd (h : nat) (a : acs) (m : list (nat * acs)) : list (nat * acs) :=
  (h, a) :: filter (fun q => negb (Nat.eqb (fst q) h)) m.
Definition hstate (m : list (nat * acs)) (dflt : acs) (h : nat) : acs :=
  match hlookup m h with Some a => a | None => dflt end.

(* [pjs J p]: [p] with each [PVia j js lo karms k] reading its join state from [J j] ([js] while
   [J] has none).  The certificate checks [pjs J (psh f p)] with every join state computed. *)
Section Joins.
  Variable J : nat -> option acs.
  Fixpoint pjs (p : plan) : plan :=
    match p with
    | PRun stops k => PRun stops (pjs k)
    | PSplit e mid k1 k2 => PSplit e mid (pjs k1) (pjs k2)
    | PCase2 e mid k1 k2 => PCase2 e mid (pjs k1) (pjs k2)
    | PCaseDisj b1 b2 k1 k2 => PCaseDisj b1 b2 (pjs k1) (pjs k2)
    | PShDisj b1 n1 b2 n2 k => PShDisj b1 n1 b2 n2 (pjs k)
    | PContra => PContra
    | PFact K k => PFact K (pjs k)
    | PJoin b off n k => PJoin b off n (pjs k)
    | PForget ixs k => PForget ixs (pjs k)
    | PDropRange b n k => PDropRange b n (pjs k)
    | PGcKeep ws k => PGcKeep ws (pjs k)
    | PBump m k => PBump m (pjs k)
    | PHavoc rs k => PHavoc rs (pjs k)
    | PHavocBig K k => PHavocBig K (pjs k)
    | PFresh r logc base k => PFresh r logc base (pjs k)
    | PSys y k => PSys y (pjs k)
    | PMmap k => PMmap (pjs k)
    | PMmapIn k => PMmapIn (pjs k)
    | PMprotect k => PMprotect (pjs k)
    | PBrk2 a b => PBrk2 (pjs a) (pjs b)
    | PX x args k => PX x args (pjs k)
    | PExt id args k => PExt id args (pjs k)
    | PEmit id args k => PEmit id args (pjs k)
    | PExt2 id args k1 k2 => PExt2 id args (pjs k1) (pjs k2)
    | PLoop J0 N inv body k => PLoop J0 N inv (pjs body) (pjs k)
    | PNext => PNext
    | PHandoff h => PHandoff h
    | PExit => PExit
    | PFog i sz k => PFog i sz (pjs k)
    | PFogNew i sz k => PFogNew i sz (pjs k)
    | PGhost b n k => PGhost b n (pjs k)
    | PUnvis b n k => PUnvis b n (pjs k)
    | PHavocBrk lo hi k => PHavocBrk lo hi (pjs k)
    | PIntro lo hi k => PIntro lo hi (pjs k)
    | PDiamond joinpc rs k => PDiamond joinpc rs (pjs k)
    | PRename m k => PRename m (pjs k)
    | PCompact k => PCompact (pjs k)
    | PVia j js lo karms k => PVia j (match J j with Some a => a | None => js end) lo (pjs karms) (pjs k)
    | PMerge j => PMerge j
    | PAbstractCell b n k => PAbstractCell b n (pjs k)
    | PHavocWords bs k => PHavocWords bs (pjs k)
    | PRespell r e k => PRespell r e (pjs k)
    end.
End Joins.

(* a join state's facts restricted to those [PMerge]'s test accepts: [check]'s [PMerge j] arm tests
   [entails_h lo (nxt js) cs js], which needs every fact of the join state to name only variables
   below the via's [lo] ([kn_vars_lt]) *)
Definition keep_lt (lo : option nat) (cs : acs) : acs :=
  match lo with
  | Some b => set_kn cs (filter (kentry_vars_lt b) (kn cs))
  | None => cs
  end.

(* the fixed rule: [cs]'s facts that name a launch variable and no fresh one, and its other facts
   (on a fresh variable, or naming no variable: [kentry_vars_lt 0]) that the recorded state [rec],
   renumbered by [f], names too *)
Definition filt_rec (f : nat -> nat) (nx0 : nat) (rec : option acs) (cs : acs) : acs :=
  match rec with
  | Some r =>
      let rk := map (ksh f) (kn r) in
      set_kn cs (filter (fun K : kentry => ((kentry_vars_lt nx0 K && negb (kentry_vars_lt 0 K)) || existsb (kentry_eqb K) rk)%bool) (kn cs))
  | None => cs
  end.

(* [run js] is a certificate's own check with hand-off map [js] (a plan with no PVia): a missing
   state becomes the reached one; a state the reached one does not entail becomes the join of the
   two; any other result stops and leaves the table as it is. *)
Fixpoint collect_handoffs (fuel : nat) (run : (nat -> option acs) -> cres) (m : list (nat * acs)) : list (nat * acs) :=
  match fuel with
  | O => m
  | S f =>
      match run (hlookup m) with
      | CErr code (PHandoff h) cs =>
          if Z.eqb code 4%Z then collect_handoffs f run (hupd h cs m)
          else if Z.eqb code 3%Z then
            match hlookup m h with
            | Some a => collect_handoffs f run (hupd h (join_states a cs) m)
            | None => m
            end
          else m
      | _ => m
      end
  end.

(* [collect_handoffs1]: the map [collect_handoffs] makes, from ONE run of the check instead of one
   run per state it adds (the method of reac-pw/fuzz_headamp's Reusable/PlanRegen.v).  [crun] is
   the certificate's own check written as [AsanPlan.check_coll] with [hvisit] at its hand-offs,
   started from [(fuel, m)].
   Why one run gives the same map: [check] reads its hand-off map only at [PHandoff h], a leaf, so
   which hand-offs a run reaches, in which order, and the state at each, do not depend on the map
   until the run stops at one; and a hand-off a run has passed is passed again by the next run,
   because a state that entails [a] also entails [join_states a b].  So [collect_handoffs]'s runs
   make their changes at the hand-offs in the order the run reaches them, and [hvisit] makes, at
   the hand-off reached, the changes they make there, one per unit of fuel, until the map entails
   the reached state; with the fuel spent it changes nothing more, as [collect_handoffs] stops.
   The states are checked by [check] in the certificate either way, so this decides nothing a
   certificate rests on. *)
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
Definition collect_handoffs1 (fuel : nat)
    (crun : nat * list (nat * acs) -> cres * (nat * list (nat * acs)))
    (m : list (nat * acs)) : list (nat * acs) :=
  snd (snd (crun (fuel, m))).

(* [collect_hjf1]: the hand-off states [H] and join states [J] of a run, from ONE run of the check.
   [crun] is the certificate's own check written as [AsanPlan.check_coll] with [hvisitj] at its
   hand-offs and [jvisit fl kf] and [jget] at its vias, started from the empty tables (with
   [hvisit]'s budget [fuel]).  At a hand-off, [hvisit] makes [H h] the reached state, or its join
   with the state [H h] has when that one is not entailed ([collect_handoffs1]).  At a [PMerge j]
   whose state [cs] the join state [J j] does not pass, [jvisit] makes [J j] [cs], or its join with
   [J j], keeping only the facts below the via's [lo] and those the filter [kf j] keeps, with its
   counter at least [fl j].  A join state's counter is free above its arms' counters (the [PMerge]
   test matches every register variable in [lo, nxt js)); [fl] keeps the counter the recorded join
   state had, so the via's continuation names its fresh variables as the recorded plan does.
   [check_coll] checks a via's arms before its continuation, so the continuation runs once, from
   the join state every arm has passed or changed; a join keeps the first state's registers, maps
   and pc, a subset of its knowledge and looser bounds, so an arm's state that passed [J j] passes
   it after a later change too.  The certificate checks [pjs (hlookup J) p] against the hand-off
   map [hlookup H] with [check], so these tables decide nothing a certificate rests on: a wrong
   table only makes the certificate fail. *)
Notation hjtab := ((nat * list (nat * acs)) * list (nat * acs))%type.
Definition hvisitj (h : nat) (cs : acs) (t : hjtab) : hjtab := (hvisit h cs (fst t), snd t).
Definition jget (j : nat) (t : hjtab) : option acs := hlookup (snd t) j.
Definition jvisit (fl : nat -> nat) (kf : nat -> acs -> acs) (j lo : nat) (cs : acs) (t : hjtab) : hjtab :=
  let js := match hlookup (snd t) j with Some a => join_states a cs | None => cs end in
  let js1 := kf j (keep_lt (Some lo) js) in
  (fst t, hupd j (bump js1 (fl j - nxt js1)) (snd t)).
Definition collect_hjf1 (fuel : nat) (crun : hjtab -> cres * hjtab) : list (nat * acs) * list (nat * acs) :=
  let t := snd (crun ((fuel, []), [])) in (snd (fst t), snd t).

(* the result shape of a run, or [SNil] when it refuses *)
Definition shape_of (c : cres) : shape := match c with COk s => s | CErr _ _ _ => SNil end.
