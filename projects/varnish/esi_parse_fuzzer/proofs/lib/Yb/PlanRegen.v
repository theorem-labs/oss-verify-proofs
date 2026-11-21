(* SPDX-License-Identifier: MIT *)
(* Adapted from libreac/fuzz_boxreg/proofs/lib/Reusable/PlanRegen.v (itself copied from
   cgif/cgif_file_fuzzer/proofs/lib/PlanRegen.v) and, for [collect_hj], [pjs] and [ash], from
   skcms/iccprofile_info/proofs/lib/Asan/PlanRegen.v: module paths changed, and this unit's plan
   constructor [PDiamondDisj] in the place of libreac's [PMmapIn2] and skcms's own constructors. *)
(* Making the start-up certificates' recorded data in the build rather than by hand, at
   LPS 727298f3.

   WHY: the 727298f3 launch has a longer auxv (27 or 29 pairs by the run's CONFIG_RSEQ flag),
   AT_RANDOM below the strings and more launch variables, so the states the start-up run
   hands off, and the states it joins arms at, are spelled differently from the states
   recorded against the released model.  A recorded state is therefore made again from the
   run, here, by [check] itself.

   1. [collect_handoffs]: [check]'s [PHandoff h] arm ([AsanPlan.v]) returns [CErr 4 (PHandoff
   h) cs] when its handoff map has no state for [h], and [CErr 3 (PHandoff h) cs] when the
   reached [cs] does not entail the state it has; [cs] is then the state at that handoff.
   [collect_handoffs] reruns the check: a missing state becomes the reached one, and a state
   some other path does not entail becomes the join of the two.

   2. [collect_hj]: the same, and also at a refused [PMerge j] the join state of the plan's
   [PVia j] becomes the arm's state (or its join with the one already held).

   3. [psh]: a plan's variable renumbering, a total increasing map read off the new run.

   A state computed this way is a definition, not an assumption: the certificate that names
   it re-runs the check, which must entail it; a wrong state can only make a certificate
   red. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import AxSyioe Asanz3l AsanPlan.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* The join of two states that [entails]/[entails_h] must both accept: the knowledge both
   have, the larger fresh counter, and the weaker of each ledger bound those checks compare
   ([a_totsz], [a_eager], [a_abytes] from above, [a_ylo] from below).  Registers, mappings,
   visibility, ghosts, brk, fd and the tid flag are the first state's; the checks require
   them equal.  This unit's [entails] tests the knowledge by a plain [kentry_eqb] subset
   ([Asanz3l.entails]), so the filter keeps every fact the check accepts. *)
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
(* the state at handoff [h], or [dflt] when the run never reaches it *)
Definition hstate (m : list (nat * acs)) (dflt : acs) (h : nat) : acs :=
  match hlookup m h with Some a => a | None => dflt end.

(* [psh f]: WHICH plan fields are variables, read from this unit's [check] arms
   ([AsanPlan.v]): [PBump m], [PLoop J], both sides of [PRename], [PVia lo], and every
   embedded expression and fact.  Every other nat field stays (registers, list indices, ids,
   counts, handoff and join ids).  The embedded states of [PLoop] and [PVia] are not shifted
   ([pjs] below puts computed join states in).  Soundness does not rest on this
   classification: the certificate re-checks the shifted plan. *)
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
    | PDiamondDisj b1 b2 joinpc rs k => PDiamondDisj (esh b1) (esh b2) joinpc rs (psh k)
    end.

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

(* 4. Joins.  A [PVia j js lo karms k] node checks [k] from its join state [js] and its arms
   from the current state, each arm ending at [PMerge j], where [check] returns [CErr 3
   (PMerge j) cs] when the arm's state [cs] does not entail [js].  [run H J] is the
   certificate's check with handoff map [H] and the plan's join states taken from [J] (the
   plan is a function of them, [pjs]).  A refused merge makes [J j] the arm's state, or its
   join with the state [J j] already holds; the handoff states reached from the old join
   state are dropped, since [k] is checked from [J j]. *)
Fixpoint collect_hj (fuel : nat) (run : (nat -> option acs) -> (nat -> option acs) -> cres)
    (H J : list (nat * acs)) (RJ : list nat) : list (nat * acs) * list (nat * acs) :=
  match fuel with
  | O => (H, J)
  | S f =>
      match run (hlookup H) (hlookup J) with
      | CErr code (PHandoff h) cs =>
          if Z.eqb code 4 then collect_hj f run (hupd h cs H) J RJ
          else if Z.eqb code 3 then
            match hlookup H h with
            | Some a => collect_hj f run (hupd h (join_states a cs) H) J RJ
            | None => (H, J)
            end
          else (H, J)
      | CErr code (PMerge j) cs =>
          if Z.eqb code 3 then
            let js := match hlookup J j with
                      | Some a => if existsb (Nat.eqb j) RJ then join_states a cs else cs
                      | None => cs
                      end in
            collect_hj f run [] (hupd j js J) (j :: RJ)
          else (H, J)
      | _ => (H, J)
      end
  end.

(* [pjs f J p]: [p] with each [PVia j js lo] reading its join state from [J j], or, where [J]
   has none yet, the recorded [js] renumbered by [f] (a collector's seed); the floor [lo] is
   kept (it is a variable number, which [psh] renumbers). *)
Section Joins.
  Variable f : nat -> nat.
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
    | PMmap ka kb => PMmap (pjs ka) (pjs kb)
    | PMmapIn a b c => PMmapIn (pjs a) (pjs b) (pjs c)
    | PMprotect a b => PMprotect (pjs a) (pjs b)
    | PBrk2 a b => PBrk2 (pjs a) (pjs b)
    | PX x args k => PX x args (pjs k)
    | PExt id args k => PExt id args (pjs k)
    | PEmit id args k => PEmit id args (pjs k)
    | PExt2 id args k1 k2 => PExt2 id args (pjs k1) (pjs k2)
    | PLoop J0 N inv body k => PLoop J0 N inv (pjs body) (pjs k)
    | PNext => PNext
    | PHandoff h => PHandoff h
    | PExit => PExit
    | PSpin => PSpin
    | PFog i sz k => PFog i sz (pjs k)
    | PFogNew i sz k => PFogNew i sz (pjs k)
    | PGhost b n k => PGhost b n (pjs k)
    | PUnvis b n k => PUnvis b n (pjs k)
    | PHavocBrk lo hi k => PHavocBrk lo hi (pjs k)
    | PIntro lo hi k => PIntro lo hi (pjs k)
    | PDiamond joinpc rs k => PDiamond joinpc rs (pjs k)
    | PRename m k => PRename m (pjs k)
    | PCompact k => PCompact (pjs k)
    | PVia j js lo karms k => PVia j (match J j with Some a => a | None => ash f js end) lo (pjs karms) (pjs k)
    | PMerge j => PMerge j
    | PAbstractCell b n k => PAbstractCell b n (pjs k)
    | PHavocWords bs k => PHavocWords bs (pjs k)
    | PRespell r e k => PRespell r e (pjs k)
    | PMmapInH a b c => PMmapInH (pjs a) (pjs b) (pjs c)
    | PDiamondDisj b1 b2 joinpc rs k => PDiamondDisj b1 b2 joinpc rs (pjs k)
    end.
End Joins.

(* 5. The one [PVia] of a start-up plan, as libreac/fuzz_boxreg's Reusable/PlanRegen.v reads it
   ([JS_STOP], [pvia_set], [via_arms], [via_cont]; this unit's [PDiamondDisj] in the place of
   libreac's [PMmapIn2]).  A state [via_ok] refuses (no registers), so a check stops at a
   [PVia] and returns the state there. *)
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
  | PMmap a b => PMmap (pvia_set js lo a) (pvia_set js lo b)
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
  | PDiamondDisj b1 b2 joinpc rs k => PDiamondDisj b1 b2 joinpc rs (pvia_set js lo k)
  end.

(* The arms and the continuation of the first [PVia] of a plan. *)
Fixpoint via_arms (p : plan) : option plan :=
  match p with
  | PVia _ _ _ karms _ => Some karms
  | PRun _ k | PFact _ k | PJoin _ _ _ k | PForget _ k | PDropRange _ _ k | PGcKeep _ k
  | PBump _ k | PHavoc _ k | PHavocBig _ k | PFresh _ _ _ k | PSys _ k | PX _ _ k | PExt _ _ k
  | PEmit _ _ k | PShDisj _ _ _ _ k | PFog _ _ k | PFogNew _ _ k | PGhost _ _ k | PUnvis _ _ k
  | PHavocBrk _ _ k | PIntro _ _ k | PDiamond _ _ k | PRename _ k | PCompact k
  | PAbstractCell _ _ k | PHavocWords _ k | PRespell _ _ k | PDiamondDisj _ _ _ _ k => via_arms k
  | PSplit _ _ k1 k2 | PCase2 _ _ k1 k2 | PCaseDisj _ _ k1 k2 | PExt2 _ _ k1 k2
  | PMmap k1 k2 | PMprotect k1 k2 | PBrk2 k1 k2 =>
      match via_arms k1 with Some a => Some a | None => via_arms k2 end
  | PMmapIn a b c | PMmapInH a b c =>
      match via_arms a with Some x => Some x | None => match via_arms b with Some x => Some x | None => via_arms c end end
  | PLoop _ _ _ body k => match via_arms body with Some a => Some a | None => via_arms k end
  | _ => None
  end.
Fixpoint via_cont (p : plan) : option plan :=
  match p with
  | PVia _ _ _ _ k => Some k
  | PRun _ k | PFact _ k | PJoin _ _ _ k | PForget _ k | PDropRange _ _ k | PGcKeep _ k
  | PBump _ k | PHavoc _ k | PHavocBig _ k | PFresh _ _ _ k | PSys _ k | PX _ _ k | PExt _ _ k
  | PEmit _ _ k | PShDisj _ _ _ _ k | PFog _ _ k | PFogNew _ _ k | PGhost _ _ k | PUnvis _ _ k
  | PHavocBrk _ _ k | PIntro _ _ k | PDiamond _ _ k | PRename _ k | PCompact k
  | PAbstractCell _ _ k | PHavocWords _ k | PRespell _ _ k | PDiamondDisj _ _ _ _ k => via_cont k
  | PSplit _ _ k1 k2 | PCase2 _ _ k1 k2 | PCaseDisj _ _ k1 k2 | PExt2 _ _ k1 k2
  | PMmap k1 k2 | PMprotect k1 k2 | PBrk2 k1 k2 =>
      match via_cont k1 with Some a => Some a | None => via_cont k2 end
  | PMmapIn a b c | PMmapInH a b c =>
      match via_cont a with Some x => Some x | None => match via_cont b with Some x => Some x | None => via_cont c end end
  | PLoop _ _ _ body k => match via_cont body with Some a => Some a | None => via_cont k end
  | _ => None
  end.

(* 6. The join state of a [PVia]'s arms, for arms that are not one [PCaseDisj] (this unit's
   start-up plans split their arms by [PSplit]/[PCase2] and end each in [PMerge]): the arms
   are checked from the state at the [PVia] under a join context holding [js]; [check]
   returns [CErr 3 (PMerge j) cs] at the first arm end [js] does not cover, and [js] becomes
   that end state (the first time) or its join with it.  [run js] is the certificate's own
   check of the arms under that context.  A state a later end is joined into only loses facts,
   so the arms already covered stay covered. *)
Fixpoint collect_arms (fuel : nat) (run : acs -> cres) (js : acs) (have : bool) : acs :=
  match fuel with
  | O => js
  | S f =>
      match run js with
      | CErr code (PMerge _) cs =>
          if Z.eqb code 3 then collect_arms f run (if have then join_states js cs else cs) true else js
      | _ => js
      end
  end.

(* 7. [pextmap g gh p]: [p] with every [PExt id args] reading [g id args] (a respell row whose
   cell moved with the 727298f3 launch layout) and every [PHandoff h] replaced by [gh h] (e.g. a
   [PRename] of the hand-off state's variables back to the numbers the next plan was written
   against, then the hand-off); nothing else changes.  As every rewrite here, the certificate
   re-checks the result, so a wrong row can only make it fail. *)
Section ExtMap.
  Variable g : nat -> list expr -> list expr.
  Variable gh : nat -> plan.
  Fixpoint pextmap (p : plan) : plan :=
    match p with
    | PRun stops k => PRun stops (pextmap k)
    | PSplit e mid k1 k2 => PSplit e mid (pextmap k1) (pextmap k2)
    | PCase2 e mid k1 k2 => PCase2 e mid (pextmap k1) (pextmap k2)
    | PCaseDisj b1 b2 k1 k2 => PCaseDisj b1 b2 (pextmap k1) (pextmap k2)
    | PShDisj b1 n1 b2 n2 k => PShDisj b1 n1 b2 n2 (pextmap k)
    | PContra => PContra
    | PFact K k => PFact K (pextmap k)
    | PJoin b off n k => PJoin b off n (pextmap k)
    | PForget ixs k => PForget ixs (pextmap k)
    | PDropRange b n k => PDropRange b n (pextmap k)
    | PGcKeep ws k => PGcKeep ws (pextmap k)
    | PBump m k => PBump m (pextmap k)
    | PHavoc rs k => PHavoc rs (pextmap k)
    | PHavocBig K k => PHavocBig K (pextmap k)
    | PFresh r logc base k => PFresh r logc base (pextmap k)
    | PSys y k => PSys y (pextmap k)
    | PMmap a b => PMmap (pextmap a) (pextmap b)
    | PMmapIn a b c => PMmapIn (pextmap a) (pextmap b) (pextmap c)
    | PMprotect a b => PMprotect (pextmap a) (pextmap b)
    | PBrk2 a b => PBrk2 (pextmap a) (pextmap b)
    | PX x args k => PX x args (pextmap k)
    | PExt id args k => PExt id (g id args) (pextmap k)
    | PEmit id args k => PEmit id args (pextmap k)
    | PExt2 id args k1 k2 => PExt2 id args (pextmap k1) (pextmap k2)
    | PLoop J N inv body k => PLoop J N inv (pextmap body) (pextmap k)
    | PNext => PNext
    | PHandoff h => gh h
    | PExit => PExit
    | PSpin => PSpin
    | PFog i sz k => PFog i sz (pextmap k)
    | PFogNew i sz k => PFogNew i sz (pextmap k)
    | PGhost b n k => PGhost b n (pextmap k)
    | PUnvis b n k => PUnvis b n (pextmap k)
    | PHavocBrk l h k => PHavocBrk l h (pextmap k)
    | PIntro l h k => PIntro l h (pextmap k)
    | PDiamond joinpc rs k => PDiamond joinpc rs (pextmap k)
    | PRename m k => PRename m (pextmap k)
    | PCompact k => PCompact (pextmap k)
    | PVia j js lo karms k => PVia j js lo (pextmap karms) (pextmap k)
    | PMerge j => PMerge j
    | PAbstractCell b n k => PAbstractCell b n (pextmap k)
    | PHavocWords bs k => PHavocWords bs (pextmap k)
    | PRespell r e k => PRespell r e (pextmap k)
    | PMmapInH a b c => PMmapInH (pextmap a) (pextmap b) (pextmap c)
    | PDiamondDisj b1 b2 joinpc rs k => PDiamondDisj b1 b2 joinpc rs (pextmap k)
    end.
End ExtMap.

(* A property every collected state has, read off the table: what a certificate's [HS h =
   Some ch -> P ch] premise needs of a [hlookup] table. *)
Lemma hlookup_forall : forall (P : acs -> bool) m h a,
  forallb (fun q => P (snd q)) m = true -> hlookup m h = Some a -> P a = true.
Proof.
  intros P m h a. induction m as [|[h' c] m IH]; intros Hm Hl; [discriminate Hl|].
  cbn [forallb] in Hm. apply andb_prop in Hm as [Hc Hm]. unfold hlookup in Hl. cbn [find fst] in Hl.
  destruct (Nat.eqb h' h); cbn in Hl; [injection Hl as <-; exact Hc | exact (IH Hm Hl)].
Qed.
