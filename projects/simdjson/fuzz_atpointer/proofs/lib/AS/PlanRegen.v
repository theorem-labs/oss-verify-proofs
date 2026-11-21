(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11: the start-up certificate's recorded data made again in the build, at this
   port's model revision, by [check] itself (the method of cgif/cgif_file_fuzzer's PlanRegen.v and
   jsoncons/fuzz_bigint's PlanRegenK.v, for this unit's checker [Z2y.check]).

   WHY.  The revision's launch has one more plan variable ([V_GID], [NX0] 11 -> 12) and a longer
   auxv, so the start-up run allocates its fresh variables at other numbers than the run the
   recorded plan (AS/Z10g.v, AS/Z10h.v) was written against, and the states it joins two paths
   at ([PVia]) and hands off ([PHandoff]) are spelled differently from the recorded ones
   (AS/Z10e.v, Z10f.v, Z10c.v, Z10d.v).

   1. [pshd F VJ]: the plan's variables renumbered, as a total function applied where the plan is
   checked.  The plan renames its variables at each [PRename] (a compaction), so the map is one
   per compaction depth ([F], depth 0 first), each a monotone step map read off the new run by a
   probe, never chosen.  The same pass puts in each [PVia]'s join state from [VJ].

   2. [regen]: the join and hand-off states, collected by rerunning the check.  A [PVia] whose join
   state is [JS_STOP] fails ([via_ok] wants 32 registers) and returns the state there; its join
   state is then the join of its arms' end states ([merge]), which [PMerge] returns when it
   refuses.  A [PHandoff] with no state returns the state there ([CErr 4]); a reached state the
   recorded one does not cover returns it too ([CErr 3]) and the two are joined.

   A state made this way is a definition, not an assumption: the certificate that names it checks
   the plan again, and [check] must accept every state; a wrong state can only make it red. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z78 Z2z Z2y.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Section Shift.
  Variable f : nat -> nat.
  Fixpoint esh (e : expr) : expr :=
    match e with
    | ELit _ => e | EVar v => EVar (f v)
    | EAlu op a b => EAlu op (esh a) (esh b) | EAluw op a b => EAluw op (esh a) (esh b)
    | EMd op a b => EMd op (esh a) (esh b) | EMdw op a b => EMdw op (esh a) (esh b)
    | EExt sx lo n a => EExt sx lo n (esh a) | EBlob _ _ _ _ => e
    end.
  Definition sash (a : saddr) : saddr := SA (esh (a_base a)) (a_off a).
  Definition ksh (K : kentry) : kentry :=
    match K with
    | KWord a w v => KWord (sash a) w (esh v) | KZero a n => KZero (sash a) (esh n)
    | KBlob a n k => KBlob (sash a) (esh n) k | KImg _ _ => K
    | KAlign x m => KAlign (esh x) m | KRange x lo hi => KRange (esh x) lo hi
    | KWr a n => KWr (sash a) (esh n) | KDisj a1 n1 a2 n2 => KDisj (sash a1) (esh n1) (sash a2) (esh n2)
    | KFill a n c => KFill (sash a) (esh n) c | KUnk a n => KUnk (sash a) (esh n)
    end.
End Shift.

(* A monotone step map: [bps] lists (threshold, offset) pairs in increasing threshold order, and
   a variable takes the offset of the last threshold at or below it (none: unchanged). *)
Fixpoint bpd (bps : list (nat * nat)) (v : nat) (acc : nat) : nat :=
  match bps with [] => acc | (t, d) :: r => if Nat.leb t v then bpd r v d else acc end.
Definition bpf (bps : list (nat * nat)) (v : nat) : nat := (v + bpd bps v 0)%nat.
Definition mapd (F : list (list (nat * nat))) (d : nat) : nat -> nat := bpf (nth d F []).

(* a one-child node with its variable fields renumbered by [f] and child [k'] *)
Definition psh1 (f : nat -> nat) (p : plan) (k' : plan) : plan :=
  match p with
  | PRun st _ => PRun st k'
  | PShDisj b1 n1 b2 n2 _ => PShDisj (esh f b1) (esh f n1) (esh f b2) (esh f n2) k'
  | PFact K _ => PFact (ksh f K) k'
  | PJoin b o n _ => PJoin (esh f b) o n k'
  | PForget ixs _ => PForget ixs k'
  | PDropRange b n _ => PDropRange (esh f b) (esh f n) k'
  | PGcKeep ws _ => PGcKeep (map (fun q => (esh f (fst q), esh f (snd q))) ws) k'
  | PBump m _ => PBump (f m) k'
  | PHavoc rs _ => PHavoc rs k'
  | PHavocBig K _ => PHavocBig K k'
  | PFresh r l b _ => PFresh r l (option_map (esh f) b) k'
  | PSys y _ => PSys y k'
  | PX x a _ => PX x (map (esh f) a) k'
  | PExt i a _ => PExt i (map (esh f) a) k'
  | PEmit i a _ => PEmit i (map (esh f) a) k'
  | PFog i s _ => PFog i s k'
  | PFogNew i s _ => PFogNew i s k'
  | PGhost b n _ => PGhost (esh f b) (esh f n) k'
  | PUnvis b n _ => PUnvis (esh f b) (esh f n) k'
  | PHavocBrk lo hi _ => PHavocBrk lo hi k'
  | PIntro lo hi _ => PIntro lo hi k'
  | PDiamond j rs _ => PDiamond j rs k'
  | PCompact _ => PCompact k'
  | PAbstractCell b n _ => PAbstractCell (esh f b) n k'
  | PHavocWords bs _ => PHavocWords (map (esh f) bs) k'
  | PRespell r e _ => PRespell r (esh f e) k'
  | PHavocCell b n _ => PHavocCell (esh f b) n k'
  | PCaseDisjJ b1 b2 j rs _ => PCaseDisjJ (esh f b1) (esh f b2) j rs k'
  | PFreshAnd r _ => PFreshAnd r k'
  | PVisSlice b n _ => PVisSlice (esh f b) (esh f n) k'
  | PKWrJoin b1 o1 n1 b2 o2 n2 _ => PKWrJoin (esh f b1) o1 (esh f n1) (esh f b2) o2 (esh f n2) k'
  | PIntroW w fs _ => PIntroW w (map (ksh f) fs) k'
  | q => q
  end.

(* A state [via_ok] refuses (no registers), so a check stops at a [PVia] and returns the state
   there; and one [PMerge] refuses (pc 0), so an arm's check returns its end state. *)
Definition JS_STOP : acs := ACS (mk_ss 0 [] [] 0) [] 0 0 0 [] [] 0 (ELit 0) FdStd false.

(* The plan at compaction depth [d] renumbered by [F], with the join state of each [PVia j] that
   [VJ] names put in, and [JS_STOP] in every other one: the recorded join state is never used.
   A [PRename]'s sources are at its own depth, its targets and its continuation one deeper.  The
   plan has no [PLoop] (so no embedded loop state to renumber). *)
Fixpoint pshd (F : list (list (nat * nat))) (VJ : nat -> option acs) (d : nat) (p : plan) : plan :=
  match p with
  | PRename m k => PRename (map (fun q => (mapd F d (fst q), mapd F (S d) (snd q))) m) (pshd F VJ (S d) k)
  | PSplit e m k1 k2 => PSplit (esh (mapd F d) e) m (pshd F VJ d k1) (pshd F VJ d k2)
  | PCase2 e m k1 k2 => PCase2 (esh (mapd F d) e) m (pshd F VJ d k1) (pshd F VJ d k2)
  | PCaseDisj b1 b2 k1 k2 => PCaseDisj (esh (mapd F d) b1) (esh (mapd F d) b2) (pshd F VJ d k1) (pshd F VJ d k2)
  | PMmap a b => PMmap (pshd F VJ d a) (pshd F VJ d b)
  | PMmapIn a b c => PMmapIn (pshd F VJ d a) (pshd F VJ d b) (pshd F VJ d c)
  | PMprotect a b => PMprotect (pshd F VJ d a) (pshd F VJ d b)
  | PBrk2 a b => PBrk2 (pshd F VJ d a) (pshd F VJ d b)
  | PExt2 i a k1 k2 => PExt2 i (map (esh (mapd F d)) a) (pshd F VJ d k1) (pshd F VJ d k2)
  | PLoop J N inv b k => PLoop (mapd F d J) (esh (mapd F d) N) inv (pshd F VJ d b) (pshd F VJ d k)
  | PVia j js lo ka k =>
      PVia j (match VJ j with Some a => a | None => JS_STOP end) (mapd F d lo) (pshd F VJ d ka) (pshd F VJ d k)
  | PMmapInH a b c => PMmapInH (pshd F VJ d a) (pshd F VJ d b) (pshd F VJ d c)
  | PBrk2S a b => PBrk2S (pshd F VJ d a) (pshd F VJ d b)
  | PRun _ k | PShDisj _ _ _ _ k | PFact _ k | PJoin _ _ _ k | PForget _ k | PDropRange _ _ k | PGcKeep _ k
  | PBump _ k | PHavoc _ k | PHavocBig _ k | PFresh _ _ _ k | PSys _ k | PX _ _ k | PExt _ _ k | PEmit _ _ k
  | PFog _ _ k | PFogNew _ _ k | PGhost _ _ k | PUnvis _ _ k | PHavocBrk _ _ k | PIntro _ _ k | PDiamond _ _ k
  | PCompact k | PAbstractCell _ _ k | PHavocWords _ k | PRespell _ _ k | PHavocCell _ _ k
  | PCaseDisjJ _ _ _ _ k | PFreshAnd _ k | PVisSlice _ _ k | PKWrJoin _ _ _ _ _ _ k | PIntroW _ _ k =>
      psh1 (mapd F d) p (pshd F VJ d k)
  | q => q
  end.

Definition kentry_below (lo : nat) (K : kentry) : bool := kentry_vars_lt lo K.

(* The join of two states that [entails]/[entails_h] must both accept: the knowledge both have,
   the larger fresh counter, and the weaker of each ledger bound those checks compare.  Registers,
   mappings, visibility, brk, fd and the tid flag are the first state's; the checks require them
   equal. *)
Definition join_states (a b : acs) : acs :=
  let k := filter (fun K => existsb (kentry_eqb K) (kn b)) (kn a) in
  let ss := a_ss a in
  ACS (mk_ss (s_pc ss) (s_regs ss) k (Nat.max (nxt a) (nxt b))) (a_maps a)
      (Z.max (a_totsz a) (a_totsz b)) (Z.min (a_ylo a) (a_ylo b)) (Z.max (a_eager a) (a_eager b))
      (a_vis a) (a_ghost a) (Z.max (a_abytes a) (a_abytes b)) (a_brk a) (a_fd a) (a_tidset a).

(* A join state names below its floor [lo] only what [entails_h] lets it name: knowledge about
   variables below [lo] (the registers above it are the join's own fresh names). *)
Definition via_state (lo : nat) (a : acs) : acs := set_kn a (filter (kentry_below lo) (kn a)).

Definition hlookup (m : list (nat * acs)) (h : nat) : option acs :=
  match find (fun q => Nat.eqb (fst q) h) m with Some q => Some (snd q) | None => None end.
Definition hupd (h : nat) (a : acs) (m : list (nat * acs)) : list (nat * acs) :=
  (h, a) :: filter (fun q => negb (Nat.eqb (fst q) h)) m.

(* The end states of a [PVia]'s arms, joined: [runj js] checks the arms under a join context
   with state [js]; each [PMerge] that refuses gives one more end state.  Returns the join and
   the last answer. *)
Fixpoint merge (fuel : nat) (lo : nat) (runj : acs -> cres) (acc : option acs) : option acs * cres :=
  match fuel with
  | O => (acc, CErr 0 PContra JS_STOP)
  | S f =>
      let r := runj (match acc with Some a => a | None => JS_STOP end) in
      match r with
      | COk _ => (acc, r)
      | CErr 3 (PMerge _) e =>
          let e' := via_state lo e in
          merge f lo runj (Some (match acc with Some a => via_state lo (join_states a e') | None => e' end))
      | _ => (acc, r)
      end
  end.

(* [run VJ HL] is the certificate's own check of the renumbered plan with join states [VJ] and
   hand-off map [HL]; [arms j js lo cs ka] checks the arms [ka] of [PVia j] from [cs] under the
   join context [check] builds there. *)
Fixpoint regen (fuel : nat) (run : list (nat * acs) -> list (nat * acs) -> cres)
    (arms : list (nat * acs) -> nat -> acs -> nat -> acs -> plan -> cres)
    (VJ HL : list (nat * acs)) : list (nat * acs) * list (nat * acs) * cres :=
  match fuel with
  | O => (VJ, HL, CErr 0 PContra JS_STOP)
  | S f =>
      let r := run VJ HL in
      match r with
      | CErr 3 (PVia j _ lo ka _) cs =>
          match hlookup VJ j with
          | Some _ => (VJ, HL, r)
          | None =>
              match fst (merge 40 lo (fun js => arms HL j js lo cs ka) None) with
              | Some js => regen f run arms (hupd j js VJ) HL
              | None => (VJ, HL, r)
              end
          end
      | CErr 3 (PMerge j) cs =>
          match hlookup VJ j with
          | Some a => regen f run arms (hupd j (join_states a cs) VJ) HL
          | None => (VJ, HL, r)
          end
      | CErr 4 (PHandoff h) cs => regen f run arms VJ (hupd h cs HL)
      | CErr 3 (PHandoff h) cs =>
          match hlookup HL h with
          | Some a => regen f run arms VJ (hupd h (join_states a cs) HL)
          | None => (VJ, HL, r)
          end
      | _ => (VJ, HL, r)
      end
  end.
