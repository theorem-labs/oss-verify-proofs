(* SPDX-License-Identifier: MIT *)
(* Copied from projects/skcms/iccprofile_info/proofs/lib/Asan/PlanRegen.v (itself a copy of
   projects/jsoncons/fuzz_bigint/proofs/lib/PlanRegenK.v), with the module paths changed to
   speex/speex_decode_fuzzer_float; [psh] and [pjs] follow this unit's plan type (no PBrkU, PDisjDia,
   PWordFresh or PCaseDisjO; PHavocCell, PBrk2S, PCaseDisjJ, PFreshAnd, PVisSlice, PKWrJoin and PIntroW
   added), [kentry] has no KInv, [psh] takes one map per stretch of the plan between two [PRename]s,
   the join states of [PVia]/[PMerge] are collected before the hand-off states ([collect_js]), and
   [hvisit] (one run of the check for the hand-off states and the shape: [coll_map], [coll_shape])
   follows reac-pw/fuzz_headamp's Reusable/PlanRegen.v.

   Regenerating the start-up certificate's data in the build rather than by hand:
   a plan's variable renumbering, and the states a run reaches at its joins and hand-offs.

   1. [psh fs]: a plan's variable renumbering, as total functions applied where the plan is checked,
   so a recorded plan is not rewritten by hand.

   WHY: LPS 727298f3 gives the launch two more plan variables ([APC.V_G] = 10, [APC.V_GID] = 11:
   [APC.NX0] is 12, not 10) and more of the auxv to read, so the start-up run allocates its fresh
   variables at other numbers than the run the recorded plan was written against, and a plan that
   names a fresh variable then names the wrong one.  The maps are read off the new run (a probe that
   stops the run where the plan names the variable and prints the state), never chosen.

   This unit's plan compacts its variables twice with [PRename] (a rename's sources are the numbers of
   the stretch before it, its targets those of the stretch after it), so [psh] takes a list of maps:
   the first renumbers the plan up to the first [PRename] and that rename's sources, the next one its
   targets and the stretch after it, and so on; the last map stays in force.

   WHICH plan fields are variables: read from the checker's arms ([AP.check], lib/AS/X0lh.v) --
   PBump m, PLoop J, PRename m (both sides), PVia lo; every embedded expr and kentry (PIntroW's facts
   too).  Every other nat field stays: registers (PHavoc, PFresh, PFreshAnd, PDiamond, PRespell,
   PCaseDisjJ), list indices (PForget), ids (PExt, PEmit, PExt2, PHandoff, PMerge, PVia j, PFog,
   PFogNew), counts (PJoin, PHavocBig, PHavocCell).  The embedded states of PLoop and PVia are not
   shifted by [psh]; [ash] shifts a state.
   SOUNDNESS DOES NOT REST ON THIS CLASSIFICATION: the certificates vm_compute through [psh] and
   re-check the shifted plan; a wrong map or classification can only make a certificate fail. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0m4 X0li X0lh.
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

  (* A whole state, renumbered: a collector's seed, never a recorded value. *)
  Definition fdsh (d : afd) : afd :=
    match d with FdFile k l o => FdFile k (esh l) (esh o) | _ => d end.
  Definition ash (cs : acs) : acs :=
    let ss := a_ss cs in
    ACS (SSR (s_pc ss) (map esh (s_regs ss)) (s_log ss) (map ksh (s_know ss)) (f (s_next ss)) (option_map sash (s_resv ss)))
        (map (fun m => AM (esh (am_base m)) (esh (am_len m)) (am_kind m)) (a_maps cs))
        (a_totsz cs) (a_ylo cs) (a_eager cs) (map pesh (a_vis cs)) (map pesh (a_ghost cs)) (a_abytes cs)
        (esh (a_brk cs)) (fdsh (a_fd cs)) (a_tidset cs).
End Shift.

(* the map in force, and the maps after the next [PRename] *)
Definition fcur (fs : list (nat -> nat)) : nat -> nat := match fs with f :: _ => f | [] => fun v => v end.
Definition fnext (fs : list (nat -> nat)) : list (nat -> nat) :=
  match fs with _ :: ((_ :: _) as r) => r | _ => fs end.

Fixpoint psh (fs : list (nat -> nat)) (p : plan) : plan :=
  let f := fcur fs in
  match p with
  | PRun stops k => PRun stops (psh fs k)
  | PSplit e mid k1 k2 => PSplit (esh f e) mid (psh fs k1) (psh fs k2)
  | PCase2 e mid k1 k2 => PCase2 (esh f e) mid (psh fs k1) (psh fs k2)
  | PCaseDisj b1 b2 k1 k2 => PCaseDisj (esh f b1) (esh f b2) (psh fs k1) (psh fs k2)
  | PShDisj b1 n1 b2 n2 k => PShDisj (esh f b1) (esh f n1) (esh f b2) (esh f n2) (psh fs k)
  | PContra => PContra
  | PFact K k => PFact (ksh f K) (psh fs k)
  | PJoin b off n k => PJoin (esh f b) off n (psh fs k)
  | PForget ixs k => PForget ixs (psh fs k)
  | PDropRange b n k => PDropRange (esh f b) (esh f n) (psh fs k)
  | PGcKeep ws k => PGcKeep (map (pesh f) ws) (psh fs k)
  | PBump m k => PBump (f m) (psh fs k)
  | PHavoc rs k => PHavoc rs (psh fs k)
  | PHavocBig K k => PHavocBig K (psh fs k)
  | PFresh r logc base k => PFresh r logc (option_map (esh f) base) (psh fs k)
  | PSys y k => PSys y (psh fs k)
  | PMmap ka kb => PMmap (psh fs ka) (psh fs kb)
  | PMmapIn a b c => PMmapIn (psh fs a) (psh fs b) (psh fs c)
  | PMprotect a b => PMprotect (psh fs a) (psh fs b)
  | PBrk2 a b => PBrk2 (psh fs a) (psh fs b)
  | PX x args k => PX x (map (esh f) args) (psh fs k)
  | PExt id args k => PExt id (map (esh f) args) (psh fs k)
  | PEmit id args k => PEmit id (map (esh f) args) (psh fs k)
  | PExt2 id args k1 k2 => PExt2 id (map (esh f) args) (psh fs k1) (psh fs k2)
  | PLoop J N inv body k => PLoop (f J) (esh f N) inv (psh fs body) (psh fs k)
  | PNext => PNext
  | PHandoff h => PHandoff h
  | PExit => PExit
  | PSpin => PSpin
  | PFog i sz k => PFog i sz (psh fs k)
  | PFogNew i sz k => PFogNew i sz (psh fs k)
  | PGhost b n k => PGhost (esh f b) (esh f n) (psh fs k)
  | PUnvis b n k => PUnvis (esh f b) (esh f n) (psh fs k)
  | PHavocBrk lo hi k => PHavocBrk lo hi (psh fs k)
  | PIntro lo hi k => PIntro lo hi (psh fs k)
  | PDiamond joinpc rs k => PDiamond joinpc rs (psh fs k)
  | PRename m k => PRename (map (fun q => (f (fst q), fcur (fnext fs) (snd q))) m) (psh (fnext fs) k)
  | PCompact k => PCompact (psh fs k)
  | PVia j js lo karms k => PVia j js (f lo) (psh fs karms) (psh fs k)
  | PMerge j => PMerge j
  | PAbstractCell b n k => PAbstractCell (esh f b) n (psh fs k)
  | PHavocWords bs k => PHavocWords (map (esh f) bs) (psh fs k)
  | PRespell r e k => PRespell r (esh f e) (psh fs k)
  | PMmapInH a b c => PMmapInH (psh fs a) (psh fs b) (psh fs c)
  | PHavocCell b n k => PHavocCell (esh f b) n (psh fs k)
  | PBrk2S a b => PBrk2S (psh fs a) (psh fs b)
  | PCaseDisjJ b1 b2 joinpc rs k => PCaseDisjJ (esh f b1) (esh f b2) joinpc rs (psh fs k)
  | PFreshAnd r k => PFreshAnd r (psh fs k)
  | PVisSlice b n k => PVisSlice (esh f b) (esh f n) (psh fs k)
  | PKWrJoin b1 o1 n1 b2 o2 n2 k => PKWrJoin (esh f b1) o1 (esh f n1) (esh f b2) o2 (esh f n2) (psh fs k)
  | PIntroW w fs0 k => PIntroW w (map (ksh f) fs0) (psh fs k)
  end.

(* 2. Joins.  A [PVia j js lo karms k] node checks [k] from its join state [js] and its arms from the
   current state, each arm ending at [PMerge j], where [check] returns [CErr 3 (PMerge j) cs] when the
   arm's state [cs] does not entail [js] ([entails_h], lib/AS/X0li.v).  [pjs J p] is [p] with each
   [PVia j js] reading its join state from [J j] (the recorded state where [J] has none), as coturn's
   [Asan/MainCol.v] [pjs] does; [pjs_arms J p] is the same with each [PVia]'s [k] replaced by the
   hand-off [JH + j], which the hand-off map of [run_arms] answers with [J j] itself, so that the run
   checks the arms against [J] without walking the code after the join.  The join states are
   collected with [pjs_arms] first ([collect_js]), the hand-off states after them with [pjs]
   ([collect_handoffs]): a hand-off state is reached from a join state, never the other way. *)
Definition JH : nat := 7000.

Section Joins.
  Variable J : nat -> option acs.
  Fixpoint pjs_gen (arms_only : bool) (p : plan) : plan :=
    match p with
    | PRun stops k => PRun stops (pjs_gen arms_only k)
    | PSplit e mid k1 k2 => PSplit e mid (pjs_gen arms_only k1) (pjs_gen arms_only k2)
    | PCase2 e mid k1 k2 => PCase2 e mid (pjs_gen arms_only k1) (pjs_gen arms_only k2)
    | PCaseDisj b1 b2 k1 k2 => PCaseDisj b1 b2 (pjs_gen arms_only k1) (pjs_gen arms_only k2)
    | PShDisj b1 n1 b2 n2 k => PShDisj b1 n1 b2 n2 (pjs_gen arms_only k)
    | PContra => PContra
    | PFact K k => PFact K (pjs_gen arms_only k)
    | PJoin b off n k => PJoin b off n (pjs_gen arms_only k)
    | PForget ixs k => PForget ixs (pjs_gen arms_only k)
    | PDropRange b n k => PDropRange b n (pjs_gen arms_only k)
    | PGcKeep ws k => PGcKeep ws (pjs_gen arms_only k)
    | PBump m k => PBump m (pjs_gen arms_only k)
    | PHavoc rs k => PHavoc rs (pjs_gen arms_only k)
    | PHavocBig K k => PHavocBig K (pjs_gen arms_only k)
    | PFresh r logc base k => PFresh r logc base (pjs_gen arms_only k)
    | PSys y k => PSys y (pjs_gen arms_only k)
    | PMmap ka kb => PMmap (pjs_gen arms_only ka) (pjs_gen arms_only kb)
    | PMmapIn a b c => PMmapIn (pjs_gen arms_only a) (pjs_gen arms_only b) (pjs_gen arms_only c)
    | PMprotect a b => PMprotect (pjs_gen arms_only a) (pjs_gen arms_only b)
    | PBrk2 a b => PBrk2 (pjs_gen arms_only a) (pjs_gen arms_only b)
    | PX x args k => PX x args (pjs_gen arms_only k)
    | PExt id args k => PExt id args (pjs_gen arms_only k)
    | PEmit id args k => PEmit id args (pjs_gen arms_only k)
    | PExt2 id args k1 k2 => PExt2 id args (pjs_gen arms_only k1) (pjs_gen arms_only k2)
    | PLoop J0 N inv body k => PLoop J0 N inv (pjs_gen arms_only body) (pjs_gen arms_only k)
    | PNext => PNext
    | PHandoff h => PHandoff h
    | PExit => PExit
    | PSpin => PSpin
    | PFog i sz k => PFog i sz (pjs_gen arms_only k)
    | PFogNew i sz k => PFogNew i sz (pjs_gen arms_only k)
    | PGhost b n k => PGhost b n (pjs_gen arms_only k)
    | PUnvis b n k => PUnvis b n (pjs_gen arms_only k)
    | PHavocBrk lo hi k => PHavocBrk lo hi (pjs_gen arms_only k)
    | PIntro lo hi k => PIntro lo hi (pjs_gen arms_only k)
    | PDiamond joinpc rs k => PDiamond joinpc rs (pjs_gen arms_only k)
    | PRename m k => PRename m (pjs_gen arms_only k)
    | PCompact k => PCompact (pjs_gen arms_only k)
    | PVia j js lo karms k =>
        PVia j (match J j with Some a => a | None => js end) lo (pjs_gen arms_only karms)
             (if arms_only then PHandoff (JH + j) else pjs_gen arms_only k)
    | PMerge j => PMerge j
    | PAbstractCell b n k => PAbstractCell b n (pjs_gen arms_only k)
    | PHavocWords bs k => PHavocWords bs (pjs_gen arms_only k)
    | PRespell r e k => PRespell r e (pjs_gen arms_only k)
    | PMmapInH a b c => PMmapInH (pjs_gen arms_only a) (pjs_gen arms_only b) (pjs_gen arms_only c)
    | PHavocCell b n k => PHavocCell b n (pjs_gen arms_only k)
    | PBrk2S a b => PBrk2S (pjs_gen arms_only a) (pjs_gen arms_only b)
    | PCaseDisjJ b1 b2 joinpc rs k => PCaseDisjJ b1 b2 joinpc rs (pjs_gen arms_only k)
    | PFreshAnd r k => PFreshAnd r (pjs_gen arms_only k)
    | PVisSlice b n k => PVisSlice b n (pjs_gen arms_only k)
    | PKWrJoin b1 o1 n1 b2 o2 n2 k => PKWrJoin b1 o1 n1 b2 o2 n2 (pjs_gen arms_only k)
    | PIntroW w fs k => PIntroW w fs (pjs_gen arms_only k)
    end.
  Definition pjs : plan -> plan := pjs_gen false.
  Definition pjs_arms : plan -> plan := pjs_gen true.
  (* the hand-off map of a [pjs_arms] run: hand-off [JH + j] answers with the join state [J j] *)
  Definition HJ (h : nat) : option acs := if Nat.leb JH h then J (h - JH) else None.
End Joins.

(* 3. The states a run reaches, computed from the run.  [check]'s [PHandoff h] arm returns
   [CErr 4 (PHandoff h) cs] when its hand-off map has no state for [h], and [CErr 3 (PHandoff h) cs]
   when the reached [cs] does not entail the state it has; its [PMerge j] arm returns
   [CErr 3 (PMerge j) cs] when the arm's [cs] does not entail the join state.  [cs] is then the state
   there.  A state computed this way is a definition, not an assumption: the certificate that names it
   re-runs the check, which must entail it. *)

Definition hlookup (m : list (nat * acs)) (h : nat) : option acs :=
  match find (fun q => Nat.eqb (fst q) h) m with Some q => Some (snd q) | None => None end.
Definition hupd (h : nat) (a : acs) (m : list (nat * acs)) : list (nat * acs) :=
  (h, a) :: filter (fun q => negb (Nat.eqb (fst q) h)) m.

(* The join of two states at one hand-off.  [entails] (lib/AS/X0li.v) needs equal registers,
   mappings, visibility, ghosts, brk, fd and tid flag, a subset of the knowledge by [kentry_eqb], and
   the accounting bounds no tighter than the arrival's; the join is the first state with the knowledge
   both have and the looser of each bound. *)
Definition join_states (a b : acs) : acs :=
  ACS (mk_ss (pc a) (s_regs (a_ss a)) (filter (fun K => existsb (kentry_eqb K) (kn b)) (kn a)) (Nat.max (nxt a) (nxt b)))
      (a_maps a) (Z.max (a_totsz a) (a_totsz b)) (Z.min (a_ylo a) (a_ylo b)) (Z.max (a_eager a) (a_eager b))
      (a_vis a) (a_ghost a) (Z.max (a_abytes a) (a_abytes b)) (a_brk a) (a_fd a) (a_tidset a).

(* The join of two arm states at one [PMerge].  The merge's own test of the knowledge is
   [kn_incl_h], one fact at a time by [kn_incl1_h]: the join keeps each fact of the first state that
   the second state's knowledge passes by that test, so it keeps every fact the merge accepts. *)
Definition join_js (A : atable) (a b : acs) : acs :=
  ACS (mk_ss (pc a) (s_regs (a_ss a)) (filter (kn_incl1_h A (kn b)) (kn a)) (Nat.max (nxt a) (nxt b)))
      (a_maps a) (Z.max (a_totsz a) (a_totsz b)) (Z.min (a_ylo a) (a_ylo b)) (Z.max (a_eager a) (a_eager b))
      (a_vis a) (a_ghost a) (Z.max (a_abytes a) (a_abytes b)) (a_brk a) (a_fd a) (a_tidset a).

(* [run J] is the certificate's check of [pjs_arms J] with hand-off map [HJ J], from the table
   [J0] of seeds.  A refused merge makes [J j] the arm's state, or, once a run has already put an arm's
   state there, its join with it. *)
Fixpoint collect_js (A : atable) (fuel : nat) (run : (nat -> option acs) -> cres)
    (J : list (nat * acs)) (RJ : list nat) : list (nat * acs) :=
  match fuel with
  | O => J
  | S f =>
      match run (hlookup J) with
      | CErr code (PMerge j) cs =>
          if Z.eqb code 3%Z then
            let js := match hlookup J j with
                      | Some a => if existsb (Nat.eqb j) RJ then join_js A a cs else cs
                      | None => cs
                      end in
            collect_js A f run (hupd j js J) (j :: RJ)
          else J
      | _ => J
      end
  end.

(* [run H] is the certificate's own check with hand-off map [H]. *)
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

(* The one-run collector (reac-pw/fuzz_headamp's Reusable/PlanRegen.v [hvisit]): the map
   [collect_handoffs] makes, from ONE run of the check instead of one run per state it adds.  The
   run is the certificate's own check written as [AP.check_coll] (lib/AS/X0lh.v) with [hvisit] at
   its hand-offs, started from [(fuel, m)].  Why one run gives the same map: [check] reads its
   map only at [PHandoff h], a leaf, so the hand-offs a run reaches, in order, and the state at
   each, do not depend on the map until the run stops at one.  A hand-off a run has passed is
   passed again by the next run: only the state at the [h] just changed is new, and a state that
   entails [a] entails [join_states a b] ([join_states] keeps [a]'s registers, mappings,
   visibility, ghosts, brk, fd and tid flag, a part of its knowledge and looser bounds).  So
   [collect_handoffs]'s runs make their changes at the hand-offs in the order the run reaches
   them, and [hvisit] makes, at the hand-off reached, the changes they make there, one per unit of
   fuel, until the map entails the reached state; then the run goes on.  With the fuel spent it
   changes nothing more, as [collect_handoffs] stops.  Soundness does not rest on this: the
   certificates check every hand-off state with [check]. *)
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
(* A [check_coll] run's result: [coll_map] is its map (the map [collect_handoffs] makes);
   [coll_shape] is its answer's shape, which is [check]'s answer with that map wherever every
   hand-off state there is entailed (a certificate checks this with [check]). *)
Definition coll_map (rm : cres * (nat * list (nat * acs))) : list (nat * acs) := snd (snd rm).
Definition coll_shape (rm : cres * (nat * list (nat * acs))) : shape :=
  match fst rm with COk s => s | CErr _ _ _ => SNil end.

(* A property every collected state has, read off the table: what a certificate's [HS h = Some ch ->
   P ch] premise needs of a [hlookup] table. *)
Lemma hlookup_forall : forall (P : acs -> bool) m h a,
  forallb (fun q => P (snd q)) m = true -> hlookup m h = Some a -> P a = true.
Proof.
  intros P m h a. induction m as [|[h' c] m IH]; intros Hm Hl; [discriminate Hl|].
  cbn [forallb] in Hm. apply andb_prop in Hm as [Hc Hm]. unfold hlookup in Hl. cbn [find fst] in Hl.
  destruct (Nat.eqb h' h); cbn in Hl; [injection Hl as <-; exact Hc | exact (IH Hm Hl)].
Qed.
