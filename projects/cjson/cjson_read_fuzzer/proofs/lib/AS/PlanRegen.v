(* SPDX-License-Identifier: MIT *)
(* Made from projects/jsoncons/fuzz_bigint/proofs/lib/PlanRegenK.v and
   projects/double-conversion/string_to_double_fuzzer/proofs/lib/PlanRegen.v (their LPS 727298f3
   start-up certificate regeneration), over this unit's plan and state types.

   Regenerating the start-up certificates' data in the build rather than by hand: a plan's
   variable renumbering, and the states a run hands off.

   1. [psh f]: a plan's variable renumbering, as a total function applied where the plan is
   checked, so a recorded plan is not rewritten by hand.  LPS 727298f3 gives the launch more plan
   variables ([V_G] and [V_GID]: NX0 11 -> 13) and more of the auxv to read, so the runs allocate
   their fresh variables at other numbers than the runs the recorded plans were written against.
   Each map is read off the new run (a probe that stops the run where the plan names a variable
   and prints the state), never chosen.

   WHICH plan fields are variables: read from [AsanPlan.check]'s arms -- PBump m, PLoop J,
   PRename m (both sides), PVia lo; every embedded expr and kentry.  Every other nat field stays:
   registers (PHavoc, PFresh, PDiamond, PRespell), list indices (PForget, PFog, PFogNew), ids
   (PExt, PEmit, PExt2, PHandoff, PMerge, PVia j), counts (PJoin, PHavocBig).  The embedded
   states of PLoop and PVia are renumbered by [ash].
   SOUNDNESS DOES NOT REST ON THIS CLASSIFICATION: the certificates vm_compute through [psh] and
   re-check the renumbered plan; a wrong map or classification can only make a certificate fail.

   2. [collect_handoffs]: the states a run hands off, computed from the run.  [check]'s
   [PHandoff h] arm returns [CErr 4 (PHandoff h) cs] when its hand-off map has no state for [h],
   and [CErr 3 (PHandoff h) cs] when the reached [cs] does not entail the state it has; [cs] is
   then the state at that hand-off.  A state computed this way is a definition, not an
   assumption: the certificate that names it re-runs the check, which must entail it. *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan.
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
  Definition amsh (m : amap) : amap := AM (esh (am_base m)) (esh (am_len m)) (am_kind m).
  Definition fdsh (d : afd) : afd :=
    match d with FdFile k len off => FdFile k (esh len) (esh off) | _ => d end.
  Definition sesh (e : sentry) : sentry := SE (sash (e_addr e)) (e_width e) (esh (e_val e)).
  (* a state's renumbering; its fresh counter moves with the map *)
  Definition ash (cs : acs) : acs :=
    let ss := a_ss cs in
    ACS (SSR (s_pc ss) (map esh (s_regs ss)) (map sesh (s_log ss)) (map ksh (s_know ss)) (f (s_next ss))
             (option_map sash (s_resv ss)))
        (map amsh (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs) (map pesh (a_vis cs))
        (map pesh (a_ghost cs)) (a_abytes cs) (esh (a_brk cs)) (fdsh (a_fd cs)) (a_tidset cs).

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
    | PLoop J N inv body k => PLoop (f J) (esh N) (ash inv) (psh body) (psh k)
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
    | PVia j js lo karms k => PVia j (ash js) (f lo) (psh karms) (psh k)
    | PMerge j => PMerge j
    | PAbstractCell b n k => PAbstractCell (esh b) n (psh k)
    | PHavocWords bs k => PHavocWords (map esh bs) (psh k)
    | PRespell r e k => PRespell r (esh e) (psh k)
    | PMmapInH a b c => PMmapInH (psh a) (psh b) (psh c)
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

(* A total increasing map given as a table read from the new run: ascending thresholds [(t, d)] in the OLD
   numbering; an old variable [v] moves by the [d] of the last [t <= v], and by 0 below the first threshold. *)
Fixpoint tbl_d (tbl : list (nat * nat)) (v acc : nat) : nat :=
  match tbl with [] => acc | (t, d) :: r => if Nat.leb t v then tbl_d r v d else acc end.
Definition tshift (tbl : list (nat * nat)) (v : nat) : nat := (v + tbl_d tbl v 0)%nat.

(* The join of two states at one hand-off.  [AsanPlanCore.entails] needs equal registers,
   mappings, visibility, ghosts, brk, fd and tid flag, a subset of the knowledge ([kn_sub_idx]),
   and bounds on four sizes; so the join is the first state with the knowledge both have and the
   four sizes at their weaker ends. *)
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

(* [run js] is the certificate's own check with hand-off map [js].  A missing state becomes the
   reached one; a state the reached one does not entail becomes the join of the two; any other
   result stops and leaves the table as it is (so a refused node shows as a failing
   certificate). *)
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
Definition hstate (m : list (nat * acs)) (dflt : acs) (h : nat) : acs :=
  match hlookup m h with Some a => a | None => dflt end.

(* the result shape of a run, or [SNil] when it refuses *)
Definition shape_of (c : cres) : shape := match c with COk s => s | CErr _ _ _ => SNil end.

(* [pmapH h]: replace the first node, on every path, at which [h] answers [Some q] by [q] (the
   rest of the plan unchanged).  Copied from projects/msgpack-c/unpack_pack_fuzzer/proofs/lib/AS/
   PlanRegen.v, whose plan type has the same constructors.  Used to change one recorded node chain
   by a fixed rule computed in the build; the certificate re-checks the result. *)
Section H.
Variable h : plan -> option plan.
Fixpoint pmapH (p : plan) : plan :=
  match h p with Some q => q | None =>
  match p with
  | PRun st k => PRun st (pmapH k)
  | PSplit e m k1 k2 => PSplit e m (pmapH k1) (pmapH k2)
  | PCase2 e m k1 k2 => PCase2 e m (pmapH k1) (pmapH k2)
  | PCaseDisj b1 b2 k1 k2 => PCaseDisj b1 b2 (pmapH k1) (pmapH k2)
  | PShDisj b1 n1 b2 n2 k => PShDisj b1 n1 b2 n2 (pmapH k)
  | PContra => PContra
  | PFact K k => PFact K (pmapH k)
  | PJoin b o n k => PJoin b o n (pmapH k)
  | PForget ixs k => PForget ixs (pmapH k)
  | PDropRange b n k => PDropRange b n (pmapH k)
  | PGcKeep ws k => PGcKeep ws (pmapH k)
  | PBump m k => PBump m (pmapH k)
  | PHavoc rs k => PHavoc rs (pmapH k)
  | PHavocBig K k => PHavocBig K (pmapH k)
  | PFresh r l b k => PFresh r l b (pmapH k)
  | PSys y k => PSys y (pmapH k)
  | PMmap a b => PMmap (pmapH a) (pmapH b)
  | PMmapIn a b c => PMmapIn (pmapH a) (pmapH b) (pmapH c)
  | PMprotect a b => PMprotect (pmapH a) (pmapH b)
  | PBrk2 a b => PBrk2 (pmapH a) (pmapH b)
  | PX x a k => PX x a (pmapH k)
  | PExt i a k => PExt i a (pmapH k)
  | PEmit i a k => PEmit i a (pmapH k)
  | PExt2 i a k1 k2 => PExt2 i a (pmapH k1) (pmapH k2)
  | PLoop J N inv b k => PLoop J N inv (pmapH b) (pmapH k)
  | PNext => PNext
  | PHandoff x => PHandoff x
  | PExit => PExit
  | PSpin => PSpin
  | PFog i s k => PFog i s (pmapH k)
  | PFogNew i s k => PFogNew i s (pmapH k)
  | PGhost b n k => PGhost b n (pmapH k)
  | PUnvis b n k => PUnvis b n (pmapH k)
  | PHavocBrk lo hi k => PHavocBrk lo hi (pmapH k)
  | PIntro lo hi k => PIntro lo hi (pmapH k)
  | PDiamond j rs k => PDiamond j rs (pmapH k)
  | PRename m k => PRename m (pmapH k)
  | PCompact k => PCompact (pmapH k)
  | PVia j js lo a k => PVia j js lo (pmapH a) (pmapH k)
  | PMerge j => PMerge j
  | PAbstractCell b n k => PAbstractCell b n (pmapH k)
  | PHavocWords bs k => PHavocWords bs (pmapH k)
  | PRespell r e k => PRespell r e (pmapH k)
  | PMmapInH a b c => PMmapInH (pmapH a) (pmapH b) (pmapH c)
  end end.
End H.

(* The AT_RANDOM copy's split chain (segment Q, AsanBoot.v and BothBoot.v).  The recorded plan splits
   [e_atr8] into one generic branch up to the old range's top and one branch per value above it,
   registers 13 and 14 respelled as the literals the old run gave.  [e_atr8]'s range in the computed
   start state ends lower, and the generic branch cannot read the shadow word near that top.  The
   chain is made again by msgpack-c/unpack_pack_fuzzer's rule (its AsanStartupCertC.v) from the
   computed state, in the build: generic [g] up to [top - 7], then one branch for each of the seven
   top values, each respelling registers 13 and 14 as the literals the run gives in that branch,
   read with the branch cut at [PHandoff (900 + k)] (both registers have one value there: [xlo] =
   [xhi]).  The certificate re-checks the result. *)
Definition atr8_top (cs : acs) : Z :=
  match find (fun K => match K with KRange x _ _ => expr_eqb x e_atr8 | _ => false end) (kn cs) with
  | Some (KRange _ _ hi) => hi | _ => 0%Z end.
Definition is_chain (p : plan) : bool :=
  match p with PSplit e m _ _ => (expr_eqb e e_atr8 && Z.eqb m 17592186044384)%bool | _ => false end.
Fixpoint chain_from (i : Z) (ls : list plan) : plan :=
  match ls with [] => PContra | [l] => l | l :: rest => PSplit e_atr8 i l (chain_from (i + 1)%Z rest) end.
Definition chain (g : plan) (t : Z) (ls : list plan) : plan := PSplit e_atr8 (t - 7)%Z g (chain_from (t - 6)%Z ls).
Definition swap_chain (q : plan) (p : plan) : option plan := if is_chain p then Some q else None.
Definition chain_cuts : list plan := map (fun k => PHandoff (900 + k)%nat) (seq 0 7).
Definition rlit (t : list (nat * acs)) (k : nat) : option Z * option Z * option Z * option Z :=
  match hlookup t (900 + k)%nat with
  | Some cs => (xlo (kn cs) (reg cs 13), xhi (kn cs) (reg cs 13), xlo (kn cs) (reg cs 14), xhi (kn cs) (reg cs 14))
  | None => (None, None, None, None) end.
Definition leaf (q2 : plan) (q : option Z * option Z * option Z * option Z) : plan :=
  match q with
  | (Some a, Some b, Some c, Some d) =>
      if (Z.eqb a b && Z.eqb c d)%bool then PRespell 13 (ELit a) (PRespell 14 (ELit c) q2) else PContra
  | _ => PContra end.
