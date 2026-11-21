(* SPDX-License-Identifier: MIT *)
(* Made from jsoncons/fuzz_bigint's PlanRegenK.v (its 727298f3 start-up certificate regeneration),
   over this unit's plan and state types.

   Regenerating the start-up certificates' data in the build rather than by hand
   (the method of jsoncons/fuzz_bigint's PlanRegenK.v): a plan's variable renumbering, and the
   states a run hands off.

   1. [psh f]: a plan's variable renumbering, as a total function applied where the plan is
   checked, so a recorded plan is not rewritten by hand.  LPS 727298f3 gives the launch more plan
   variables ([V_G], [V_R], [V_GID]: NX0 10 -> 13) and more of the auxv to read, so the runs
   allocate their fresh variables at other numbers than the runs the recorded plans were written
   against.  The map is read off the new run (a probe that stops the run where the plan names a
   variable and prints the state), never chosen.

   WHICH plan fields are variables: read from [AsanPlan.check]'s arms -- PBump m, PLoop J,
   PRename m (both sides), PVia lo, PCompactFrom b, PZonesD/PCaseDisjD m, PGhostCover's alias
   indices; every embedded expr and kentry.  Every other nat field stays: registers, list
   indices, ids, counts, fuel.  The embedded states of PLoop and PVia are shifted by [ash].
   SOUNDNESS DOES NOT REST ON THIS CLASSIFICATION: the certificates vm_compute through [psh] and
   re-check the shifted plan; a wrong map or classification can only make a certificate red. *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import APC. Import AP.

Section Shift.
  Variable f : nat -> nat.
  (* [holes t]: a plan the caller supplies itself at [PTail t], left unshifted (a recorded node
     that names plan variables of the NEW numbering, which no total map of the old numbering
     reaches: the launch variables [V_G], [V_R], [V_GID] at 10..12).  [kref]: the refused child of
     a recorded [PSys YMunmap k], when the run derives one; [None] continues with [k] in both. *)
  Variable holes : nat -> option plan.
  Variable kref : option plan.

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
  Definition amsh (m : amap) : amap := AM (esh (am_base m)) (esh (am_len m)) (am_kind m).
  Definition fdsh (d : afd) : afd :=
    match d with FdFile k len off => FdFile k (esh len) (esh off) | _ => d end.
  (* a state's renumbering; its fresh counter moves with the map *)
  Definition ash (cs : acs) : acs :=
    let ss := a_ss cs in
    ACS (SSR (s_pc ss) (map esh (s_regs ss)) (s_log ss) (map ksh (s_know ss)) (f (s_next ss))
             (option_map sash (s_resv ss)))
        (map amsh (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs) (map pesh (a_vis cs))
        (map pesh (a_ghost cs)) (a_abytes cs) (esh (a_brk cs)) (fdsh (a_fd cs)) (a_tidset cs).

  (* [sf]: what a state embedded in the plan ([PLoop]'s invariant, [PVia]'s join state) becomes:
     [ash] when the plan is renumbered with the states it carries; the identity when those states
     are already in the new numbering (the main phase's states are renumbered where they are
     defined, [MainRegenAsan.mreg]). *)
  Variable sf : acs -> acs.
  (* [kf]: keep the plan's [PForget] nodes.  The main phase's are lists of knowledge INDICES into
     the old run's state; the new run's knowledge differs from it in a few places along a path
     (probe record, section "Main phase"), so an index there can name another fact than the one
     the old run dropped.  A [PForget] only weakens the state, so a plan checked without them is
     checked as soundly; a compaction ([PRename]) may need the facts the [PForget] dropped gone.
     The main phase's forms check [mplan p] and, when that check fails, [mplanD p]
     ([AsanMainDefs.cres_or]); the start-up plans keep theirs. *)
  Variable kf : bool.

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
    | PForget ixs k => if kf then PForget ixs (psh k) else psh k
    | PDropRange b n k => PDropRange (esh b) (esh n) (psh k)
    | PGcKeep ws k => PGcKeep (map pesh ws) (psh k)
    | PBump m k => PBump (f m) (psh k)
    | PHavoc rs k => PHavoc rs (psh k)
    | PHavocBig K k => PHavocBig K (psh k)
    | PFresh r logc base k => PFresh r logc (option_map esh base) (psh k)
    (* LPS 08b1429: munmap can be refused (-ENOMEM), so [PSys YMunmap] declines and the exact-entry
       munmap is [PMunmap2 krefused kgranted]; a recorded [PSys YMunmap k] continues with [k] in
       the granted child, and with [kref] (else [k]) in the refused one *)
    | PSys y k => match y with
                  | YMunmap => PMunmap2 (match kref with Some q => q | None => psh k end) (psh k)
                  | _ => PSys y (psh k)
                  end
    | PMmap ka kb => PMmap (psh ka) (psh kb)
    | PMmapIn a b c => PMmapIn (psh a) (psh b) (psh c)
    | PMprotect a b => PMprotect (psh a) (psh b)
    | PBrk2 a b => PBrk2 (psh a) (psh b)
    | PMunmap2 a b => PMunmap2 (psh a) (psh b)
    | PX x args k => PX x (map esh args) (psh k)
    | PLib k => PLib (psh k)
    | PExt id args k => PExt id (map esh args) (psh k)
    | PEmit id args k => PEmit id (map esh args) (psh k)
    | PExt2 id args k1 k2 => PExt2 id (map esh args) (psh k1) (psh k2)
    | PLoop J N inv body k => PLoop (f J) (esh N) (sf inv) (psh body) (psh k)
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
    | PVia j js lo karms k => PVia j (sf js) (f lo) (psh karms) (psh k)
    | PMerge j => PMerge j
    | PAbstractCell b n k => PAbstractCell (esh b) n (psh k)
    | PHavocWords bs k => PHavocWords (map esh bs) (psh k)
    | PRespell r e k => PRespell r (esh e) (psh k)
    | PMmapInH a b c => PMmapInH (psh a) (psh b) (psh c)
    | PBytes b off n k => PBytes (esh b) off n (psh k)
    | PJoinV b off n k => PJoinV (esh b) off n (psh k)
    | PZones e k => PZones (esh e) (psh k)
    | PZoneHull e k => PZoneHull (esh e) (psh k)
    | PVisCut b N n1 k => PVisCut (esh b) N n1 (psh k)
    | PFactC K s cert k => PFactC (ksh K) s (map (fun q => (fst q, esh (snd q))) cert) (psh k)
    | PZonesD e joinpc rs m k => PZonesD (esh e) joinpc rs (f m) (psh k)
    | PIntroEq wit lo hi k => PIntroEq (esh wit) lo hi (psh k)
    | PGhostCover L al k => PGhostCover (map pesh L) (map (fun q => (f (fst q), esh (snd q))) al) (psh k)
    | PCaseDisjD b1 b2 joinpc rs m k => PCaseDisjD (esh b1) (esh b2) joinpc rs (f m) (psh k)
    | PKeepOnly bs rs k => PKeepOnly (map esh bs) rs (psh k)
    | PTail t => match holes t with Some q => q | None => PTail t end
    | PNameWord b lo hi k => PNameWord (esh b) lo hi (psh k)
    | PCompactFrom b k => PCompactFrom (f b) (psh k)
    | PDiamondX joinpc rs opsa opsb k =>
        PDiamondX joinpc rs (map (fun q => (fst q, map esh (snd q))) opsa) (map (fun q => (fst q, map esh (snd q))) opsb) (psh k)
    | PRunF n stops k => PRunF n stops (psh k)
    | PTailF t => PTailF t
    | PFullTail k => PFullTail (psh k)
    end.
End Shift.

(* a recorded plan renumbered by [f] with no node of its own, its states renumbered with it *)
Definition pshf (f : nat -> nat) : plan -> plan := psh f (fun _ => None) None (ash f) true.

(* the renumbering every map here has: the identity below [t], then [+ d] *)
Definition vshift (t d : nat) (v : nat) : nat := if Nat.ltb v t then v else (v + d)%nat.

(* a total monotone map given as a table read from a probe: ascending thresholds [(t, d)] in the
   OLD numbering, an old variable [v] moves by the [d] of the last [t <= v] (by 0 below the first) *)
Fixpoint tbl_d (tbl : list (nat * nat)) (v acc : nat) : nat :=
  match tbl with [] => acc | (t, d) :: r => if Nat.leb t v then tbl_d r v d else acc end.
Definition tshift (tbl : list (nat * nat)) (v : nat) : nat := (v + tbl_d tbl v 0)%nat.

(* The numbering from the start-up hand-off on.  The hand-off compaction renames every live
   variable to the first indices at and above NX0, and the main phase names [MainItab]'s
   [T_VAR]/[V_TF]/[V_ST] there; NX0 moved from 10 to 13 (three launch variables: [V_G], [V_R],
   [V_GID]), so every recorded index at or above 10 of that numbering moves by 3. *)
Definition hand_f : nat -> nat := vshift 10 3.

(* The main phase's recorded plans in that numbering, renumbered where the main phase checks them
   ([AsanMainDefs]/[BothMainDefs] forms, [AsanMain]/[BothMain] [mtree_ok]).  The states a plan
   carries are the main phase's recorded states, renumbered where each is defined
   ([MainRegenAsan.mreg]/[MainRegenBoth.mreg]), so [mplan] leaves them as they are.  [mexpr]: an
   expression a main-phase tree or state names outside a plan. *)
Definition mplan : plan -> plan := psh hand_f (fun _ => None) None (fun s => s) true.
Definition mplanD : plan -> plan := psh hand_f (fun _ => None) None (fun s => s) false.
Definition mexpr : expr -> expr := esh hand_f.

(* 2. The states a run hands off, computed from the run.  [check]'s [PHandoff h] arm returns
   [CErr 4 (PHandoff h) cs] when its handoff map has no state for [h], and
   [CErr 3 (PHandoff h) cs] when the reached [cs] does not entail the state it has; [cs] is then
   the state at that handoff.  [collect_handoffs] reruns the check: a missing state becomes the
   reached one, and a state some other path (or the other CONFIG_RSEQ value) does not entail
   becomes the join of the two.  A state computed this way is a definition, not an assumption:
   the certificate that names it re-runs the check, which must entail it. *)

(* The join of two states at one handoff.  [AsanPlanCore.entails] needs equal registers,
   mappings, visibility, ghosts, brk, fd and tid flag, a subset of the knowledge, and bounds on
   four sizes; so the join is the first state with the knowledge both have and the four sizes at
   their weaker ends. *)
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

(* [run js] is the certificate's own check with handoff map [js].  [key h] is the entry hand-off
   [h] reads and writes: the identity, or a map that sends hand-offs the certificate gives one
   state (as [KindHSAsan.HS_kind_1 := HS_kind_0]) to one entry. *)
Fixpoint collect_k (key : nat -> nat) (fuel : nat) (run : (nat -> option acs) -> cres) (m : list (nat * acs)) : list (nat * acs) :=
  match fuel with
  | O => m
  | S f =>
      match run (fun h => hlookup m (key h)) with
      | CErr code (PHandoff h) cs =>
          if Z.eqb code 4%Z then collect_k key f run (hupd (key h) cs m)
          else if Z.eqb code 3%Z then
            match hlookup m (key h) with
            | Some a => collect_k key f run (hupd (key h) (join_states a cs) m)
            | None => m
            end
          else m
      | _ => m
      end
  end.
Definition collect_handoffs : nat -> ((nat -> option acs) -> cres) -> list (nat * acs) -> list (nat * acs) :=
  collect_k (fun h => h).

(* several runs against one map (the CONFIG_RSEQ values, or a segment's start states): the map
   one run leaves is where the next starts, until none moves it *)
Fixpoint collect_runs (key : nat -> nat) (fuel : nat) (runs : list ((nat -> option acs) -> cres)) (m : list (nat * acs)) : list (nat * acs) :=
  match fuel with
  | O => m
  | S f => collect_runs key f runs (fold_left (fun m0 run => collect_k key 20 run m0) runs m)
  end.

(* 3. The knowledge a computed hand-off state keeps.  A state the run reaches holds every fact the
   run derived; the recorded abstraction the later plans were written against kept fewer (its
   compactions list the variables live there).  Fixed rule (approved for this port by the
   implementer): keep every fact of the run that names launch variables only (below NX0), and a
   fact naming a fresh variable only when the recorded state, renumbered, has the same fact.
   Every kept fact is the run's own, so the state stays entailed by the run; the certificate
   that names it re-checks that. *)
Fixpoint evars_of (e : expr) : list nat :=
  match e with
  | ELit _ | EBlob _ _ _ _ => []
  | EVar v => [v]
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars_of a ++ evars_of b
  | EExt _ _ _ a => evars_of a
  end.
Definition kvars_of (K : kentry) : list nat :=
  match K with
  | KWord a _ v => evars_of (a_base a) ++ evars_of v
  | KZero a n | KBlob a n _ | KWr a n | KFill a n _ | KUnk a n => evars_of (a_base a) ++ evars_of n
  | KImg _ _ => []
  | KAlign x _ | KRange x _ _ => evars_of x
  | KDisj a1 n1 a2 n2 => evars_of (a_base a1) ++ evars_of n1 ++ evars_of (a_base a2) ++ evars_of n2
  end.
(* The kept facts are laid out in the recorded state's order, then the run's other
   launch-variable facts: plans address knowledge by index ([PForget], with indices up to 650 in
   the recorded main-phase plans), so an index of the recorded state names the same fact here.
   A recorded fact the run lacks is replaced IN PLACE: a fact on launch variables only by the
   run's fact about the same place ([counterpart]: same kind, same address or same expression),
   so that the run updates or drops it where the old run did the recorded one (a write to the
   stack drops the stack's [KWr] fact, an index-based [PForget] drops an argv pointer word); any
   other by [KTRUE], a fact that holds in every state. *)
Definition KTRUE : kentry := KRange (ELit 0) 0 0.
Definition launch_only (nx0 : nat) (K : kentry) : bool := forallb (fun v => Nat.ltb v nx0) (kvars_of K).
Definition kin (K : kentry) (l : list kentry) : bool := existsb (kentry_eqb K) l.
Definition same_key (K K' : kentry) : bool :=
  match K, K' with
  | KWord a w _, KWord a' w' _ => andb (saddr_eqb a a') (Nat.eqb w w')
  | KWr a _, KWr a' _ | KZero a _, KZero a' _ | KUnk a _, KUnk a' _ => saddr_eqb a a'
  | KBlob a _ _, KBlob a' _ _ | KFill a _ _, KFill a' _ _ => saddr_eqb a a'
  | KRange e _ _, KRange e' _ _ | KAlign e _, KAlign e' _ => expr_eqb e e'
  | KImg lo _, KImg lo' _ => Z.eqb lo lo'
  | KDisj a _ b _, KDisj a' _ b' _ => andb (saddr_eqb a a') (saddr_eqb b b')
  | _, _ => false
  end.
Definition counterpart (pool : list kentry) (K : kentry) : kentry :=
  match find (same_key K) pool with Some K' => K' | None => KTRUE end.
Definition keep_facts (nx0 : nat) (tmpl a : acs) : acs :=
  let pool := filter (fun K => andb (launch_only nx0 K) (negb (kin K (kn tmpl)))) (kn a) in
  let k1 := map (fun K => if kin K (kn a) then K else if launch_only nx0 K then counterpart pool K else KTRUE) (kn tmpl) in
  let k2 := filter (fun K => negb (kin K k1)) pool in
  let k' := k1 ++ k2 in
  let ss := a_ss a in
  ACS (SSR (s_pc ss) (s_regs ss) (s_log ss) k' (s_next ss) (s_resv ss))
      (a_maps a) (a_totsz a) (a_ylo a) (a_eager a) (a_vis a) (a_ghost a) (a_abytes a) (a_brk a) (a_fd a) (a_tidset a).

(* 4. The main phase's recorded states in the new launch layout.  Every recorded main-phase state
   is renumbered by [hand_f] and carries facts on the launch variables that the old launch layout
   gave and the new one does not ([D], read off the recorded main hand-off state against the one
   seg_u's run reaches), and lacks the new layout's ([L], the other way round).  [relaunch D L]
   replaces each [D] fact in place by its [counterpart] in [L] (or [KTRUE]), as [keep_facts] does,
   and puts last the [L] facts that name a launch variable and are no [D] fact's counterpart (a
   counterpart of a [D] fact the state no longer carries is left out with it: the old run had
   dropped that fact there).  An [L] fact that names no variable (a [KImg] piece, a word at a
   fixed address: the new hand-off state holds some 250 of them that the recorded one does not)
   is not put last: it is a fact about the image's memory at the hand-off, which the main phase
   writes, so a later recorded state, which the old run reached after those writes, cannot carry
   it (the probe record of this port).  A
   register that holds the value a [D] word fact gives (the old layout's argv pointer, also with
   its argc guard taken off) holds its counterpart's value instead ([vmap]).  Every kept or added
   fact and every register is checked again by the certificate that uses the state. *)
Definition vmap (D L : list kentry) : list (expr * expr) :=
  flat_map (fun K => match K, counterpart L K with
                     | KWord _ _ v, KWord _ _ v' =>
                         (v, v') :: match v, v' with EMd _ _ x, EMd _ _ x' => [(x, x')] | _, _ => [] end
                     | _, _ => []
                     end) D.
Definition erepl1 (m : list (expr * expr)) (e : expr) : expr :=
  match find (fun q => expr_eqb (fst q) e) m with Some q => snd q | None => e end.
Definition var_free (K : kentry) : bool := match kvars_of K with [] => true | _ => false end.
Definition relaunch (D L : list kentry) (S : acs) : acs :=
  let ss := a_ss S in
  let S1 := ACS (SSR (s_pc ss) (map (erepl1 (vmap D L)) (s_regs ss)) (s_log ss) (s_know ss) (s_next ss) (s_resv ss))
                (a_maps S) (a_totsz S) (a_ylo S) (a_eager S) (a_vis S) (a_ghost S) (a_abytes S) (a_brk S) (a_fd S) (a_tidset S) in
  let k1 := map (fun K => if kin K D then counterpart L K else K) (kn S) in
  set_kn S1 (k1 ++ filter (fun K => andb (negb (var_free K)) (andb (negb (kin K k1)) (negb (existsb (fun Kd => same_key Kd K) D)))) L).

(* The four size bounds a state carries ([a_totsz], [a_ylo], [a_eager], [a_abytes]: what is mapped
   in all, the lowest mapping address, the eager and the accounted bytes) move by what the launch
   moved them: the computed main hand-off state's value less the recorded one's (each later
   mapping sits where the old one did, relative to the launch's). *)
Definition resize (dt dy de da : Z) (S : acs) : acs :=
  ACS (a_ss S) (a_maps S) (a_totsz S + dt)%Z (a_ylo S + dy)%Z (a_eager S + de)%Z (a_vis S) (a_ghost S)
      (a_abytes S + da)%Z (a_brk S) (a_fd S) (a_tidset S).

(* 5. A recorded [PForget] that the new run applies to another fact than the old run did.  The
   main phase's forget lists are indices into the knowledge the old run held there; where the new
   run's knowledge before such a node differs from the old one's (a store the new run splits a
   [KImg] piece at, a fact the new launch has more or less), the same index names another fact.
   Fixed rule, applied in the build along each path of a plan to a given hand-off: at each
   [PForget] on that path, an index that names a fact with no variable which the recorded
   hand-off state carries is left out of the list ([forget_keep]).  A [PForget] only weakens a
   state, so any index list checks as soundly; the certificate re-runs the check on the plan this
   gives (the probe record of this port names the run that showed it: k1s0x into hand-off 105). *)
Definition kids (p : plan) : list plan :=
  match p with
  | PRun _ k | PShDisj _ _ _ _ k | PFact _ k | PJoin _ _ _ k | PForget _ k | PDropRange _ _ k | PGcKeep _ k
  | PBump _ k | PHavoc _ k | PHavocBig _ k | PFresh _ _ _ k | PSys _ k | PX _ _ k | PLib k | PExt _ _ k
  | PEmit _ _ k | PFog _ _ k | PFogNew _ _ k | PGhost _ _ k | PUnvis _ _ k | PHavocBrk _ _ k | PIntro _ _ k
  | PDiamond _ _ k | PRename _ k | PCompact k | PAbstractCell _ _ k | PHavocWords _ k | PRespell _ _ k
  | PBytes _ _ _ k | PJoinV _ _ _ k | PZones _ k | PZoneHull _ k | PVisCut _ _ _ k | PFactC _ _ _ k
  | PZonesD _ _ _ _ k | PIntroEq _ _ _ k | PGhostCover _ _ k | PCaseDisjD _ _ _ _ _ k | PKeepOnly _ _ k
  | PNameWord _ _ _ k | PCompactFrom _ k | PDiamondX _ _ _ _ k | PRunF _ _ k | PFullTail k => [k]
  | PSplit _ _ a b | PCase2 _ _ a b | PCaseDisj _ _ a b | PMmap a b | PMprotect a b | PBrk2 a b | PMunmap2 a b
  | PExt2 _ _ a b | PLoop _ _ _ a b | PVia _ _ _ a b => [a; b]
  | PMmapIn a b c | PMmapInH a b c => [a; b; c]
  | _ => []
  end.
(* [p] with its child [i] replaced by [q] *)
Definition setk (p : plan) (i : nat) (q : plan) : plan :=
  let pick (j : nat) (x : plan) : plan := if Nat.eqb i j then q else x in
  match p with
  | PRun s _ => PRun s q | PShDisj a b c d _ => PShDisj a b c d q | PFact K _ => PFact K q
  | PJoin a b c _ => PJoin a b c q | PForget l _ => PForget l q | PDropRange a b _ => PDropRange a b q
  | PGcKeep w _ => PGcKeep w q | PBump m _ => PBump m q | PHavoc r _ => PHavoc r q | PHavocBig K _ => PHavocBig K q
  | PFresh a b c _ => PFresh a b c q | PSys y _ => PSys y q | PX x a _ => PX x a q | PLib _ => PLib q
  | PExt i0 a _ => PExt i0 a q | PEmit i0 a _ => PEmit i0 a q | PFog a b _ => PFog a b q | PFogNew a b _ => PFogNew a b q
  | PGhost a b _ => PGhost a b q | PUnvis a b _ => PUnvis a b q | PHavocBrk a b _ => PHavocBrk a b q
  | PIntro a b _ => PIntro a b q | PDiamond a b _ => PDiamond a b q | PRename m _ => PRename m q
  | PCompact _ => PCompact q | PAbstractCell a b _ => PAbstractCell a b q | PHavocWords a _ => PHavocWords a q
  | PRespell a b _ => PRespell a b q | PBytes a b c _ => PBytes a b c q | PJoinV a b c _ => PJoinV a b c q
  | PZones e _ => PZones e q | PZoneHull e _ => PZoneHull e q | PVisCut a b c _ => PVisCut a b c q
  | PFactC a b c _ => PFactC a b c q | PZonesD a b c d _ => PZonesD a b c d q | PIntroEq a b c _ => PIntroEq a b c q
  | PGhostCover a b _ => PGhostCover a b q | PCaseDisjD a b c d e _ => PCaseDisjD a b c d e q
  | PKeepOnly a b _ => PKeepOnly a b q | PNameWord a b c _ => PNameWord a b c q | PCompactFrom b _ => PCompactFrom b q
  | PDiamondX a b c d _ => PDiamondX a b c d q | PRunF n s _ => PRunF n s q | PFullTail _ => PFullTail q
  | PSplit e m a b => PSplit e m (pick 0%nat a) (pick 1%nat b)
  | PCase2 e m a b => PCase2 e m (pick 0%nat a) (pick 1%nat b)
  | PCaseDisj x y a b => PCaseDisj x y (pick 0%nat a) (pick 1%nat b)
  | PMmap a b => PMmap (pick 0%nat a) (pick 1%nat b)
  | PMprotect a b => PMprotect (pick 0%nat a) (pick 1%nat b)
  | PBrk2 a b => PBrk2 (pick 0%nat a) (pick 1%nat b)
  | PMunmap2 a b => PMunmap2 (pick 0%nat a) (pick 1%nat b)
  | PExt2 i0 x a b => PExt2 i0 x (pick 0%nat a) (pick 1%nat b)
  | PLoop J N inv a b => PLoop J N inv (pick 0%nat a) (pick 1%nat b)
  | PVia j js lo a b => PVia j js lo (pick 0%nat a) (pick 1%nat b)
  | PMmapIn a b c => PMmapIn (pick 0%nat a) (pick 1%nat b) (pick 2%nat c)
  | PMmapInH a b c => PMmapInH (pick 0%nat a) (pick 1%nat b) (pick 2%nat c)
  | _ => p
  end.
(* every child-index path from [p] to a node [hit] picks *)
Fixpoint fpaths (fuel : nat) (hit : plan -> bool) (p : plan) : list (list nat) :=
  match fuel with
  | O => []
  | S f =>
      if hit p then [[]] else
      let fix go (i : nat) (l : list plan) : list (list nat) :=
        match l with
        | [] => []
        | q :: r => map (cons i) (fpaths f hit q) ++ go (S i) r
        end in
      go 0%nat (kids p)
  end.
Fixpoint node_on (pa : list nat) (d : nat) (p : plan) : plan :=
  match d, pa with
  | O, _ => p
  | S d', i :: pa' => node_on pa' d' (nth i (kids p) PContra)
  | S _, [] => p
  end.
(* [p] with the node at depth [d] along [pa] replaced by [q] *)
Fixpoint put_on (pa : list nat) (d : nat) (q p : plan) : plan :=
  match d, pa with
  | O, _ => q
  | S d', i :: pa' => setk p i (put_on pa' d' q (nth i (kids p) PContra))
  | S _, [] => p
  end.
Definition forget_keep (S T : acs) (ixs : list nat) : list nat :=
  filter (fun i => negb (match nth_error (kn S) i with Some K => andb (var_free K) (kin K (kn T)) | None => false end)) ixs.
(* [run q] checks [q] as the certificate does (a cut [PNext] answers [CErr 8] with the state
   there); each [PForget] on [pa], first to last, gets [forget_keep] of the state the run reaches
   at it (with the earlier ones already changed) *)
Fixpoint fix_forgets_on (run : plan -> cres) (T : acs) (pa : list nat) (ds : list nat) (p : plan) : plan :=
  match ds with
  | [] => p
  | d :: ds' =>
      let p' := match node_on pa d p with
                | PForget ixs k =>
                    match run (put_on pa d PNext p) with
                    | CErr c _ cs0 => if Z.eqb c 8%Z then put_on pa d (PForget (forget_keep cs0 T ixs) k) p else p
                    | COk _ => p
                    end
                | _ => p
                end in
      fix_forgets_on run T pa ds' p'
  end.
Definition forget_depths (pa : list nat) (p : plan) : list nat :=
  filter (fun d => match node_on pa d p with PForget _ _ => true | _ => false end) (seq 0%nat (length pa)).
Definition fix_forgets (fuel : nat) (run : plan -> cres) (T : acs) (h : nat) (p : plan) : plan :=
  fold_left (fun q pa => fix_forgets_on run T pa (forget_depths pa q) q)
            (fpaths fuel (fun q => match q with PHandoff h' => Nat.eqb h h' | _ => false end) p) p.
