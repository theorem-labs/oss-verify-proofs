(* SPDX-License-Identifier: MIT *)
(* Regenerating the start-up certificates' data in the build rather than by
   hand: a plan's variable renumbering, and the states a
   run hands off.

   1. [psh f]: a plan's variable renumbering, as a total function applied where
   the plan is checked, so a recorded plan is not rewritten by hand.

   WHY: at LPS 727298f3 the launch has more plan variables ([V_GID], NX0 = 13)
   and more of the auxv to read than the run the stored plans name their fresh
   variables for, so the start-up run allocates its fresh variables at other
   numbers.  A plan that names a fresh variable (the root plan's
   [PDropRange (escale 4096 (EVar 94)) ..]) would then name the wrong one.  The
   map for each plan is read off the run (stopped where the plan names the
   variable), never chosen; it is passed to [psh] as [f].

   WHICH plan fields are variables: the same classification as coturn's
   [Asan/VarShift.v], read from the checker's arms -- PBump m,
   PLoop J, PRename m (both sides), PVia lo; every embedded expr and kentry.
   Every other nat field stays: registers (PHavoc, PFresh, PDiamond, PRespell),
   list indices (PForget, PFog, PFogNew, PHAbs), ids (PExt, PEmit, PExt2,
   PHandoff, PMerge, PVia j), counts (PJoin, PHavocBig, PAbsWord).  The embedded
   states of PLoop and PVia are not shifted.
   SOUNDNESS DOES NOT REST ON THIS CLASSIFICATION: the certificates vm_compute
   through [psh] and re-check the shifted plan; a wrong map or classification
   can only make a certificate red. *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK.
Import ListNotations. Import AX2K. Import APCK. Import APK.

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
    | PHAbs i lo hi nlo nhi k => PHAbs i lo hi nlo nhi (psh k)
    | PAbsWord b off n lo hi k => PAbsWord (esh b) off n lo hi (psh k)
    | PMmapLH a b => PMmapLH (psh a) (psh b)
    end.
End Shift.

(* 2. The states a run hands off, computed from the run.  [check]'s [PHandoff h]
   arm ([AsanPlanK.v]) returns [CErr 4 (PHandoff h) cs] when its handoff map
   has no state for [h], and [CErr 3 (PHandoff h) cs] when the reached [cs]
   does not entail the state it has; [cs] is then the state at that handoff.
   [collect_handoffs] reruns the check: a missing state becomes the reached
   one, and a state some other path does not entail becomes the join of the
   two.  A state computed this way is a definition, not an assumption: the
   certificate that names it re-runs the check, which must entail it. *)

(* The join of two states at one handoff.  [check]'s [entails]
   ([AsanPlanCoreK.v]) needs equal registers, mappings, visibility, brk, fd and
   hop lists, and a subset of the knowledge.  Two paths to one handoff differ
   in the knowledge a [PSplit] arm keeps from its own bound: fuzz_bigint's 201
   plan reaches 202 through two arms whose states differ in two knowledge
   entries each.  So the join is the first state with the knowledge both have. *)
Definition join_states (a b : acs) : acs :=
  let a1 := set_kn a (filter (fun K => existsb (kentry_eqb K) (kn b)) (kn a)) in
  let ss := a_ss a1 in
  with_ss a1 (mk_ss (s_pc ss) (s_regs ss) (s_know ss) (Nat.max (nxt a) (nxt b))).

Definition hlookup (m : list (nat * acs)) (h : nat) : option acs :=
  match find (fun q => Nat.eqb (fst q) h) m with Some q => Some (snd q) | None => None end.
Definition hupd (h : nat) (a : acs) (m : list (nat * acs)) : list (nat * acs) :=
  (h, a) :: filter (fun q => negb (Nat.eqb (fst q) h)) m.

(* [run js] is the certificate's own check with handoff map [js]. *)
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
(* the state at handoff [h], or [dflt] when the run never reaches it *)
Definition hstate (m : list (nat * acs)) (dflt : acs) (h : nat) : acs :=
  match hlookup m h with Some a => a | None => dflt end.
