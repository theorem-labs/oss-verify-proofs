(* SPDX-License-Identifier: MIT *)
(* Made from projects/jsoncons/fuzz_bigint/proofs/lib/PlanRegenK.v of this tree, lines 2-157, with the module paths changed to skcms/iccprofile_info; psh follows this unit's plan type (no PHAbs, PAbsWord or PMmapLH; PBrkU, PDisjDia, PWordFresh and PCaseDisjO added), ksh shifts KInv's arguments, ash shifts a whole state, and collect_hj, which adds the join of a PVia/PMerge pair to collect_handoffs, replaces it; join_states also joins the accounting bounds, taking the larger a_totsz, a_eager and a_abytes and the smaller a_ylo of the two states; added fdsh, seal, HK0, nodefer, pdrop_forget, pre_ho, pjs, hlookup_forall, loop_weaken, join_states_h and collect_hjl (join and loop tables), section 5, the renaming of a state onto a recorded numbering (vunify, rn_step, on_compact, rn_rec), and section 6, the collector that merges a via's arms before its continuation (collect_hjla, pjs's deferral D); the lead comment and the comments of section 2 and of join_states are worded for this unit, and the comment of collect_handoffs is left out along with it. *)
(* Regenerating the start-up certificates' data in the build rather than by
   hand: a plan's variable renumbering, and the states a
   run hands off.

   1. [psh f]: a plan's variable renumbering, as a total function applied where
   the plan is checked, so a recorded plan is not rewritten by hand.

   WHY: LPS 727298f3 gives the launch more plan variables ([V_VDSO], [V_MSS],
   [V_GID]: the first fresh variable is [NX_HW] = 13, not 10) and more of the
   auxv to read, so the start-up run allocates its fresh variables at other
   numbers than the run the recorded plans were written against.  A plan that
   names a fresh variable then names the wrong one.  The map for each plan is
   read off the new run's state where the plan names the variable, never
   chosen; it is passed to [psh] as [f].

   WHICH plan fields are variables: read from the checker's arms -- PBump m,
   PLoop J, PRename m (both sides), PVia lo; every embedded expr and kentry.
   Every other nat field stays: registers (PHavoc, PFresh, PDiamond, PRespell,
   PDisjDia), list indices (PForget), ids (PExt, PEmit, PExt2, PHandoff,
   PMerge, PVia j, PFog, PFogNew), counts (PJoin, PHavocBig, PWordFresh).  The
   embedded states of PLoop and PVia are not shifted by [psh]; [ash] shifts a
   state.
   SOUNDNESS DOES NOT REST ON THIS CLASSIFICATION: the certificates vm_compute
   through [psh] and re-check the shifted plan; a wrong map or classification
   can only make a certificate red. *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan.
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
    | KInv id args => KInv id (map esh args)
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
    | PBrkU a b => PBrkU (psh a) (psh b)
    | PDisjDia b1 b2 o2 joinpc rs k => PDisjDia (esh b1) (esh b2) o2 joinpc rs (psh k)
    | PWordFresh b n k => PWordFresh (esh b) n (psh k)
    | PCaseDisjO b1 b2 o k1 k2 => PCaseDisjO (esh b1) (esh b2) o (psh k1) (psh k2)
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


(* [pdrop_forget p]: [p] with every [PForget] removed.  A forget only weakens the knowledge, and its
   indices point into a state's knowledge list; the recorded indices point into the earlier
   model's start-up hand-off state, whose list the computed one does not reproduce entry for
   entry.  A plan run without them keeps more facts, which every entailment test accepts. *)
Fixpoint pdrop_forget (p : plan) : plan :=
  match p with
  | PRun stops k => PRun stops (pdrop_forget k)
  | PSplit e mid k1 k2 => PSplit e mid (pdrop_forget k1) (pdrop_forget k2)
  | PCase2 e mid k1 k2 => PCase2 e mid (pdrop_forget k1) (pdrop_forget k2)
  | PCaseDisj b1 b2 k1 k2 => PCaseDisj b1 b2 (pdrop_forget k1) (pdrop_forget k2)
  | PShDisj b1 n1 b2 n2 k => PShDisj b1 n1 b2 n2 (pdrop_forget k)
  | PContra => PContra
  | PFact K k => PFact K (pdrop_forget k)
  | PJoin b off n k => PJoin b off n (pdrop_forget k)
  | PForget ixs k => pdrop_forget k
  | PDropRange b n k => PDropRange b n (pdrop_forget k)
  | PGcKeep ws k => PGcKeep ws (pdrop_forget k)
  | PBump m k => PBump m (pdrop_forget k)
  | PHavoc rs k => PHavoc rs (pdrop_forget k)
  | PHavocBig K k => PHavocBig K (pdrop_forget k)
  | PFresh r logc base k => PFresh r logc base (pdrop_forget k)
  | PSys y k => PSys y (pdrop_forget k)
  | PMmap ka kb => PMmap (pdrop_forget ka) (pdrop_forget kb)
  | PMmapIn a b c => PMmapIn (pdrop_forget a) (pdrop_forget b) (pdrop_forget c)
  | PMprotect a b => PMprotect (pdrop_forget a) (pdrop_forget b)
  | PBrk2 a b => PBrk2 (pdrop_forget a) (pdrop_forget b)
  | PX x args k => PX x args (pdrop_forget k)
  | PExt id args k => PExt id args (pdrop_forget k)
  | PEmit id args k => PEmit id args (pdrop_forget k)
  | PExt2 id args k1 k2 => PExt2 id args (pdrop_forget k1) (pdrop_forget k2)
  | PLoop J N inv body k => PLoop J N inv (pdrop_forget body) (pdrop_forget k)
  | PNext => PNext
  | PHandoff h => PHandoff h
  | PExit => PExit
  | PSpin => PSpin
  | PFog i sz k => PFog i sz (pdrop_forget k)
  | PFogNew i sz k => PFogNew i sz (pdrop_forget k)
  | PGhost b n k => PGhost b n (pdrop_forget k)
  | PUnvis b n k => PUnvis b n (pdrop_forget k)
  | PHavocBrk lo hi k => PHavocBrk lo hi (pdrop_forget k)
  | PIntro lo hi k => PIntro lo hi (pdrop_forget k)
  | PDiamond joinpc rs k => PDiamond joinpc rs (pdrop_forget k)
  | PRename m k => PRename m (pdrop_forget k)
  | PCompact k => PCompact (pdrop_forget k)
  | PVia j js lo karms k => PVia j js lo (pdrop_forget karms) (pdrop_forget k)
  | PMerge j => PMerge j
  | PAbstractCell b n k => PAbstractCell b n (pdrop_forget k)
  | PHavocWords bs k => PHavocWords bs (pdrop_forget k)
  | PRespell r e k => PRespell r e (pdrop_forget k)
  | PMmapInH a b c => PMmapInH (pdrop_forget a) (pdrop_forget b) (pdrop_forget c)
  | PBrkU a b => PBrkU (pdrop_forget a) (pdrop_forget b)
  | PDisjDia b1 b2 o2 joinpc rs k => PDisjDia b1 b2 o2 joinpc rs (pdrop_forget k)
  | PWordFresh b n k => PWordFresh b n (pdrop_forget k)
  | PCaseDisjO b1 b2 o k1 k2 => PCaseDisjO b1 b2 o (pdrop_forget k1) (pdrop_forget k2)
  end.

(* [pre_ho w p]: [p] with [w] put in front of each of its hand-offs ([PHandoff h] becomes
   [w (PHandoff h)]), so a plan can weaken the state it hands off without its recorded text
   being rewritten.  The certificate checks the plan with [w] in place, so a weakening that
   drops a fact the run needs only makes it red. *)
Fixpoint pre_ho (w : plan -> plan) (p : plan) : plan :=
  match p with
  | PRun stops k => PRun stops (pre_ho w k)
  | PSplit e mid k1 k2 => PSplit e mid (pre_ho w k1) (pre_ho w k2)
  | PCase2 e mid k1 k2 => PCase2 e mid (pre_ho w k1) (pre_ho w k2)
  | PCaseDisj b1 b2 k1 k2 => PCaseDisj b1 b2 (pre_ho w k1) (pre_ho w k2)
  | PShDisj b1 n1 b2 n2 k => PShDisj b1 n1 b2 n2 (pre_ho w k)
  | PContra => PContra
  | PFact K k => PFact K (pre_ho w k)
  | PJoin b off n k => PJoin b off n (pre_ho w k)
  | PForget ixs k => PForget ixs (pre_ho w k)
  | PDropRange b n k => PDropRange b n (pre_ho w k)
  | PGcKeep ws k => PGcKeep ws (pre_ho w k)
  | PBump m k => PBump m (pre_ho w k)
  | PHavoc rs k => PHavoc rs (pre_ho w k)
  | PHavocBig K k => PHavocBig K (pre_ho w k)
  | PFresh r logc base k => PFresh r logc base (pre_ho w k)
  | PSys y k => PSys y (pre_ho w k)
  | PMmap ka kb => PMmap (pre_ho w ka) (pre_ho w kb)
  | PMmapIn a b c => PMmapIn (pre_ho w a) (pre_ho w b) (pre_ho w c)
  | PMprotect a b => PMprotect (pre_ho w a) (pre_ho w b)
  | PBrk2 a b => PBrk2 (pre_ho w a) (pre_ho w b)
  | PX x args k => PX x args (pre_ho w k)
  | PExt id args k => PExt id args (pre_ho w k)
  | PEmit id args k => PEmit id args (pre_ho w k)
  | PExt2 id args k1 k2 => PExt2 id args (pre_ho w k1) (pre_ho w k2)
  | PLoop J N inv body k => PLoop J N inv (pre_ho w body) (pre_ho w k)
  | PNext => PNext
  | PHandoff h => w (PHandoff h)
  | PExit => PExit
  | PSpin => PSpin
  | PFog i sz k => PFog i sz (pre_ho w k)
  | PFogNew i sz k => PFogNew i sz (pre_ho w k)
  | PGhost b n k => PGhost b n (pre_ho w k)
  | PUnvis b n k => PUnvis b n (pre_ho w k)
  | PHavocBrk lo hi k => PHavocBrk lo hi (pre_ho w k)
  | PIntro lo hi k => PIntro lo hi (pre_ho w k)
  | PDiamond joinpc rs k => PDiamond joinpc rs (pre_ho w k)
  | PRename m k => PRename m (pre_ho w k)
  | PCompact k => PCompact (pre_ho w k)
  | PVia j js lo karms k => PVia j js lo (pre_ho w karms) (pre_ho w k)
  | PMerge j => PMerge j
  | PAbstractCell b n k => PAbstractCell b n (pre_ho w k)
  | PHavocWords bs k => PHavocWords bs (pre_ho w k)
  | PRespell r e k => PRespell r e (pre_ho w k)
  | PMmapInH a b c => PMmapInH (pre_ho w a) (pre_ho w b) (pre_ho w c)
  | PBrkU a b => PBrkU (pre_ho w a) (pre_ho w b)
  | PDisjDia b1 b2 o2 joinpc rs k => PDisjDia b1 b2 o2 joinpc rs (pre_ho w k)
  | PWordFresh b n k => PWordFresh b n (pre_ho w k)
  | PCaseDisjO b1 b2 o k1 k2 => PCaseDisjO b1 b2 o (pre_ho w k1) (pre_ho w k2)
  end.


(* 2. The states a run hands off, computed from the run.  [check]'s [PHandoff h]
   arm ([AsanPlanFO.v]) returns [CErr 4 (PHandoff h) cs] when its handoff map
   has no state for [h], and [CErr 3 (PHandoff h) cs] when the reached [cs]
   does not entail the state it has; [cs] is then the state at that handoff.
   The collectors below rerun the check: a missing state becomes the reached
   one, and a state some other path does not entail becomes the join of the
   two.  A state computed this way is a definition, not an assumption: the
   certificate that names it re-runs the check, which must entail it. *)

(* The join of two states at one handoff.  [check]'s [entails] needs equal
   registers, mappings, visibility, brk, fd and hop lists, a subset of the
   knowledge, and the accounting bounds no tighter than the arrival's
   ([a_totsz], [a_eager], [a_abytes] at least, [a_ylo] at most); this unit's
   [entails] has no other disjunct, so the join is the first state with the
   knowledge both have and the looser of each bound, as this unit's
   [AsanMainCertLib.acs_meet] joins them. *)
Definition join_states (a b : acs) : acs :=
  ACS (mk_ss (pc a) (s_regs (a_ss a)) (filter (fun K => existsb (kentry_eqb K) (kn b)) (kn a)) (Nat.max (nxt a) (nxt b)))
      (a_maps a) (Z.max (a_totsz a) (a_totsz b)) (Z.min (a_ylo a) (a_ylo b)) (Z.max (a_eager a) (a_eager b))
      (a_vis a) (a_ghost a) (Z.max (a_abytes a) (a_abytes b)) (a_brk a) (a_fd a) (a_tidset a).

Definition hlookup (m : list (nat * acs)) (h : nat) : option acs :=
  match find (fun q => Nat.eqb (fst q) h) m with Some q => Some (snd q) | None => None end.
Definition hupd (h : nat) (a : acs) (m : list (nat * acs)) : list (nat * acs) :=
  (h, a) :: filter (fun q => negb (Nat.eqb (fst q) h)) m.

(* the state at handoff [h], or [dflt] when the run never reaches it *)
Definition hstate (m : list (nat * acs)) (dflt : acs) (h : nat) : acs :=
  match hlookup m h with Some a => a | None => dflt end.

(* 3. Joins.  A [PVia j js lo karms k] node checks [k] from its join state [js]
   and its arms from the current state, each arm ending at [PMerge j], where
   [check] returns [CErr 3 (PMerge j) cs] when the arm's state [cs] does not
   entail [js].  [run H J] is the certificate's check with handoff map [H] and
   the plan's join states taken from [J] (the plan is a function of them).  A
   refused merge makes [J j] the arm's state, or its join with the state [J j]
   already holds, as coturn's [Asan/MainCol.v] [mc_loop] does; the handoff
   states reached from the old join state are dropped, since [k] is checked
   from [J j]. *)
Fixpoint collect_hj (fuel : nat) (run : (nat -> option acs) -> (nat -> option acs) -> cres)
    (H J : list (nat * acs)) (RJ : list nat) : list (nat * acs) * list (nat * acs) :=
  match fuel with
  | O => (H, J)
  | S f =>
      match run (hlookup H) (hlookup J) with
      | CErr code (PHandoff h) cs =>
          if Z.eqb code 4%Z then collect_hj f run (hupd h cs H) J RJ
          else if Z.eqb code 3%Z then
            match hlookup H h with
            | Some a => collect_hj f run (hupd h (join_states a cs) H) J RJ
            | None => (H, J)
            end
          else (H, J)
      | CErr code (PMerge j) cs =>
          if Z.eqb code 3%Z then
            let js := match hlookup J j with
                      | Some a => if existsb (Nat.eqb j) RJ then join_states a cs else cs
                      | None => cs
                      end in
            collect_hj f run [] (hupd j js J) (j :: RJ)
          else (H, J)
      | _ => (H, J)
      end
  end.

(* [pjs f J L D p]: [p] with each [PVia j js] reading its join state from [J j] and each
   [PLoop J0 N inv] its invariant from [L J0], or, where the table has none yet, the recorded
   state renumbered by [f] (a collector's seed).  The certificate's check is of
   [pjs f J L nodefer (psh f p)].

   A [PVia] without a join state yet is the collector's to fill: [check] runs a [PVia]'s
   continuation from its join state BEFORE its arms, and the recorded seed is the earlier
   model's state (its argv/auxv layout terms; for R4 at
   0x63514), from which the continuation can stop before any arm reaches [PMerge j].  So the
   unfilled [PVia] gets the seed with a contradictory fact ([seal]) and [PContra] as its
   continuation: the continuation is accepted, and the first arm that reaches [PMerge j] is
   refused (it does not entail the contradiction) and handed to the collector as the join
   state.  The certificate is checked with every reached [PVia] filled, so this form never
   decides a certificate.

   A filled [PVia j] whose continuation the collector defers ([D j], section 6) has the
   hand-off [HK0 + j] in place of its continuation; the certificate's plan defers none
   ([nodefer]). *)
Definition seal (a : acs) : acs := set_kn a (KRange (ELit 0) 1 0 :: kn a).
Definition HK0 : nat := 900.
Definition nodefer (j : nat) : bool := false.
Section Joins.
  Variable f : nat -> nat.
  Variable J : nat -> option acs.
  Variable L : nat -> option acs.
  Variable D : nat -> bool.
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
    | PLoop J0 N inv body k => PLoop J0 N (match L J0 with Some a => a | None => ash f inv end) (pjs body) (pjs k)
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
    | PVia j js lo karms k =>
        match J j with
        | Some a => PVia j a lo (pjs karms) (if D j then PHandoff (HK0 + j) else pjs k)
        | None => PVia j (seal (ash f js)) lo (pjs karms) PContra
        end
    | PMerge j => PMerge j
    | PAbstractCell b n k => PAbstractCell b n (pjs k)
    | PHavocWords bs k => PHavocWords bs (pjs k)
    | PRespell r e k => PRespell r e (pjs k)
    | PMmapInH a b c => PMmapInH (pjs a) (pjs b) (pjs c)
    | PBrkU a b => PBrkU (pjs a) (pjs b)
    | PDisjDia b1 b2 o2 joinpc rs k => PDisjDia b1 b2 o2 joinpc rs (pjs k)
    | PWordFresh b n k => PWordFresh b n (pjs k)
    | PCaseDisjO b1 b2 o k1 k2 => PCaseDisjO b1 b2 o (pjs k1) (pjs k2)
    end.
End Joins.

(* A property every collected state has, read off the table: what a certificate's [HS h = Some ch ->
   P ch] premise needs of a [hlookup] table. *)
Lemma hlookup_forall : forall (P : acs -> bool) m h a,
  forallb (fun q => P (snd q)) m = true -> hlookup m h = Some a -> P a = true.
Proof.
  intros P m h a. induction m as [|[h' c] m IH]; intros Hm Hl; [discriminate Hl|].
  cbn [forallb] in Hm. apply andb_prop in Hm as [Hc Hm]. unfold hlookup in Hl. cbn [find fst] in Hl.
  destruct (Nat.eqb h' h); cbn in Hl; [injection Hl as <-; exact Hc | exact (IH Hm Hl)].
Qed.

(* 4. Loop invariants.  [check]'s [PLoop J N inv body k] arm ([AsanPlanFO.v]) returns
   [CErr 3 (PLoop ..) cs] when the entry state [cs] does not entail [inst inv J 0].
   [loop_weaken J inv cs] makes the recorded invariant one the entry can satisfy:
   - a register whose recorded value names only variables below [J] (no iteration variable, no
     pattern variable of the invariant) takes the entry's value: such a register is the same on
     every iteration, and the recorded value is the earlier model's;
   - the maps, the visible and ghost pairs, the break and the file descriptor stay the
     invariant's where their instance at [J = 0] is the entry's, and are the entry's otherwise: a
     part that moves with the iteration (KW [c4_pl]: the file offset [65536 * J + 262144]) is
     kept, so the back edge's instance at [J + 1] still matches it;
   - the thread flag is the entry's, the accounting bounds the looser of the two;
   - the invariant keeps those of its facts whose instance at [J = 0] the entry holds
     ([kn_incl1_h], the entailment's own test).
   The loop body is then checked from the weakened invariant by the certificate, so a fact the
   body needs and the entry lacks makes it red, never wrong. *)
Definition loop_weaken (A : atable) (J : nat) (inv cs : acs) : acs :=
  let i0 := inst inv J (ELit 0) in
  ACS (mk_ss (pc inv)
         (map (fun q => if expr_vars_lt J (fst q) then snd q else fst q) (combine (s_regs (a_ss inv)) (s_regs (a_ss cs))))
         (filter (fun K => kn_incl1_h A (kn cs) (ksubst J (ELit 0) K)) (kn inv)) (nxt inv))
      (if list_eqb amap_eqb (a_maps i0) (a_maps cs) then a_maps inv else a_maps cs)
      (Z.max (a_totsz inv) (a_totsz cs)) (Z.min (a_ylo inv) (a_ylo cs)) (Z.max (a_eager inv) (a_eager cs))
      (if list_eqb pair_eqb (a_vis i0) (a_vis cs) then a_vis inv else a_vis cs)
      (if list_eqb pair_eqb (a_ghost i0) (a_ghost cs) then a_ghost inv else a_ghost cs)
      (Z.max (a_abytes inv) (a_abytes cs))
      (if expr_eqb (a_brk i0) (a_brk cs) then a_brk inv else a_brk cs)
      (if afd_eqb (a_fd i0) (a_fd cs) then a_fd inv else a_fd cs)
      (a_tidset cs).
(* The join of two states at a [PMerge]: [join_states] with the facts kept by the merge test's own
   inclusion ([kn_incl1_h]: an address spelled as another base plus offset, a flat or covered
   cell), not by equality: the merge refuses an arm only on what [entails_hF] reads. *)
Definition join_states_h (A : atable) (a b : acs) : acs :=
  set_kn (join_states a b) (filter (kn_incl1_h A (kn b)) (kn a)).

(* [collect_hjl]: [collect_hj] with a loop table [L] beside the join table, the plan reading
   both ([run H J L]).  A refused loop entry weakens [L J0]; hand-off states are dropped then,
   as on a refused merge, since what follows the loop is checked from the new invariant.
   Beside the three tables it returns the last run's result, the one no table update answers
   ([None] when the fuel ran out first): the certificate re-runs exactly that check. *)
Fixpoint collect_hjl (A : atable) (fuel : nat) (run : (nat -> option acs) -> (nat -> option acs) -> (nat -> option acs) -> cres)
    (H J L : list (nat * acs)) (RJ : list nat) : list (nat * acs) * list (nat * acs) * list (nat * acs) * option cres :=
  match fuel with
  | O => (H, J, L, None)
  | S f =>
      let r := run (hlookup H) (hlookup J) (hlookup L) in
      match r with
      | CErr code (PHandoff h) cs =>
          if Z.eqb code 4%Z then collect_hjl A f run (hupd h cs H) J L RJ
          else if Z.eqb code 3%Z then
            match hlookup H h with
            | Some a => collect_hjl A f run (hupd h (join_states a cs) H) J L RJ
            | None => (H, J, L, Some r)
            end
          else (H, J, L, Some r)
      | CErr code (PMerge j) cs =>
          if Z.eqb code 3%Z then
            let js := match hlookup J j with
                      | Some a => if existsb (Nat.eqb j) RJ then join_states_h A a cs else cs
                      | None => cs
                      end in
            collect_hjl A f run [] (hupd j js J) L (j :: RJ)
          else (H, J, L, Some r)
      | CErr code (PLoop J0 _ inv _ _) cs =>
          if Z.eqb code 3%Z then collect_hjl A f run [] J (hupd J0 (loop_weaken A J0 inv cs) L) RJ
          else (H, J, L, Some r)
      | _ => (H, J, L, Some r)
      end
  end.

(* 5. Renaming onto a recorded numbering.  A node whose plan compacts its variables ([PCompact])
   or renames them by a dense map of its recorded start state ([PRename (dense_map ..)]) hands
   its subtree a state whose variables the subtree's plans name by number.  The computed state at
   that step has other variables than the recorded one (the computed start-up keeps facts the
   earlier model's forgets dropped, and the run allocates other fresh variables), so the same
   compaction numbers the survivors in another order, and a survivor can be missing from the
   recorded state.

   [vunify gb cs ref] reads off the two states which variable of [cs] plays the part of which
   variable of the recorded state [ref]: registers, mappings, visible and ghost pairs, break and
   file descriptor position by position, then, pass after pass, each fact of [ref] that the facts
   of [cs] match under the pairs found so far in one way only.  Variables below [gb] are the
   launch's and must be equal.  [rn_ixs] lists the facts of [cs] that name a variable the pairs do
   not cover and that would collide with a target or lie above them all.  [rn_step] puts, in place
   of the step, a forget of those facts and the explicit rename by the pairs.  The certificate
   checks the plan with that rename in place: [node_rename] refuses a rename that is not one to
   one or that leaves a variable of the state on a target, and a wrong pair can only make a later
   node red. *)
Section Unify.
  Variable gb : nat.
  Fixpoint vs_get (v : nat) (s : list (nat * nat)) : option nat :=
    match s with [] => None | q :: r => if Nat.eqb (fst q) v then Some (snd q) else vs_get v r end.
  Definition vs_tgt (w : nat) (s : list (nat * nat)) : bool := existsb (fun q => Nat.eqb (snd q) w) s.
  Definition vbind (v w : nat) (s : list (nat * nat)) : option (list (nat * nat)) :=
    if orb (Nat.ltb v gb) (Nat.ltb w gb) then (if Nat.eqb v w then Some s else None)
    else match vs_get v s with
         | Some w' => if Nat.eqb w w' then Some s else None
         | None => if vs_tgt w s then None else Some ((v, w) :: s)
         end.
  Fixpoint eun (a b : expr) (s : list (nat * nat)) {struct a} : option (list (nat * nat)) :=
    match a, b with
    | ELit x, ELit y => if Z.eqb x y then Some s else None
    | EVar v, EVar w => vbind v w s
    | EAlu o a1 a2, EAlu o' b1 b2 =>
        if aluop_eqb o o' then match eun a1 b1 s with Some s1 => eun a2 b2 s1 | None => None end else None
    | EAluw o a1 a2, EAluw o' b1 b2 =>
        if aluop_eqb o o' then match eun a1 b1 s with Some s1 => eun a2 b2 s1 | None => None end else None
    | EMd o a1 a2, EMd o' b1 b2 =>
        if mulop_eqb o o' then match eun a1 b1 s with Some s1 => eun a2 b2 s1 | None => None end else None
    | EMdw o a1 a2, EMdw o' b1 b2 =>
        if mulop_eqb o o' then match eun a1 b1 s with Some s1 => eun a2 b2 s1 | None => None end else None
    | EExt sx lo n a1, EExt sx' lo' n' b1 =>
        if (Bool.eqb sx sx' && Nat.eqb lo lo' && Nat.eqb n n')%bool then eun a1 b1 s else None
    | EBlob _ _ _ _, EBlob _ _ _ _ => if expr_eqb a b then Some s else None
    | _, _ => None
    end.
  Definition obnd (o : option (list (nat * nat))) (k : list (nat * nat) -> option (list (nat * nat))) : option (list (nat * nat)) :=
    match o with Some s => k s | None => None end.
  Definition sun (a b : saddr) (s : list (nat * nat)) : option (list (nat * nat)) :=
    if Z.eqb (a_off a) (a_off b) then eun (a_base a) (a_base b) s else None.
  Fixpoint lun (xs ys : list expr) (s : list (nat * nat)) {struct xs} : option (list (nat * nat)) :=
    match xs, ys with
    | [], [] => Some s
    | x :: xs', y :: ys' => match eun x y s with Some s1 => lun xs' ys' s1 | None => None end
    | _, _ => None
    end.
  Definition kun (K L : kentry) (s : list (nat * nat)) : option (list (nat * nat)) :=
    match K, L with
    | KWord a w v, KWord a' w' v' => if Nat.eqb w w' then obnd (sun a a' s) (eun v v') else None
    | KZero a n, KZero a' n' => obnd (sun a a' s) (eun n n')
    | KBlob a n i, KBlob a' n' i' => if Nat.eqb i i' then obnd (sun a a' s) (eun n n') else None
    | KImg lo hi, KImg lo' hi' => if (Z.eqb lo lo' && Z.eqb hi hi')%bool then Some s else None
    | KAlign e m, KAlign e' m' => if Z.eqb m m' then eun e e' s else None
    | KRange e lo hi, KRange e' lo' hi' => if (Z.eqb lo lo' && Z.eqb hi hi')%bool then eun e e' s else None
    | KWr a n, KWr a' n' => obnd (sun a a' s) (eun n n')
    | KDisj a1 n1 a2 n2, KDisj a1' n1' a2' n2' =>
        obnd (sun a1 a1' s) (fun s1 => obnd (eun n1 n1' s1) (fun s2 => obnd (sun a2 a2' s2) (eun n2 n2')))
    | KFill a n c, KFill a' n' c' => if Z.eqb c c' then obnd (sun a a' s) (eun n n') else None
    | KUnk a n, KUnk a' n' => obnd (sun a a' s) (eun n n')
    | KInv i xs, KInv i' ys => if Nat.eqb i i' then lun xs ys s else None
    | _, _ => None
    end.
  Definition mun (m m' : amap) (s : list (nat * nat)) : option (list (nat * nat)) :=
    if mkind_eqb (am_kind m) (am_kind m') then obnd (eun (am_base m) (am_base m') s) (eun (am_len m) (am_len m')) else None.
  Definition pun (p q : expr * expr) (s : list (nat * nat)) : option (list (nat * nat)) :=
    obnd (eun (fst p) (fst q) s) (eun (snd p) (snd q)).
  Definition dun (d d' : afd) (s : list (nat * nat)) : option (list (nat * nat)) :=
    match d, d' with
    | FdFile k l o, FdFile k' l' o' => if Nat.eqb k k' then obnd (eun l l' s) (eun o o') else None
    | _, _ => Some s
    end.
  (* a position whose two sides do not match adds nothing *)
  Definition soft (o : option (list (nat * nat))) (s : list (nat * nat)) : list (nat * nat) :=
    match o with Some s' => s' | None => s end.
  Fixpoint psoft {T : Type} (u : T -> T -> list (nat * nat) -> option (list (nat * nat))) (xs ys : list T)
      (s : list (nat * nat)) : list (nat * nat) :=
    match xs, ys with
    | x :: xs', y :: ys' => psoft u xs' ys' (soft (u x y s) s)
    | _, _ => s
    end.
  Definition pairs_eqb (a b : list (nat * nat)) : bool :=
    list_eqb (fun p q => (Nat.eqb (fst p) (fst q) && Nat.eqb (snd p) (snd q))%bool) a b.
  (* the pairs that every fact of [k] matching the recorded fact [L] under [s] adds, when they all
     add the same; [None] when none adds any or two add different ones *)
  Fixpoint kext (L : kentry) (k : list kentry) (s : list (nat * nat)) (acc : option (list (nat * nat))) : option (list (nat * nat)) :=
    match k with
    | [] => acc
    | K :: k' =>
        match kun K L s with
        | Some s' =>
            if Nat.ltb (length s) (length s') then
              match acc with
              | None => kext L k' s (Some s')
              | Some s0 => if pairs_eqb s0 s' then kext L k' s acc else None
              end
            else kext L k' s acc
        | None => kext L k' s acc
        end
    end.
  Fixpoint kpass (ls k : list kentry) (s : list (nat * nat)) : list (nat * nat) :=
    match ls with
    | [] => s
    | L :: ls' => kpass ls' k (match kext L k s None with Some s' => s' | None => s end)
    end.
  Fixpoint kpasses (n : nat) (ls k : list kentry) (s : list (nat * nat)) : list (nat * nat) :=
    match n with
    | O => s
    | S n' => let s' := kpass ls k s in if Nat.eqb (length s') (length s) then s else kpasses n' ls k s'
    end.
  Definition vunify (cs ref : acs) : list (nat * nat) :=
    let s := psoft eun (s_regs (a_ss cs)) (s_regs (a_ss ref)) [] in
    let s := psoft mun (a_maps cs) (a_maps ref) s in
    let s := psoft pun (a_vis cs) (a_vis ref) s in
    let s := psoft pun (a_ghost cs) (a_ghost ref) s in
    let s := soft (eun (a_brk cs) (a_brk ref) s) s in
    let s := soft (dun (a_fd cs) (a_fd ref) s) s in
    rev (kpasses 8 (kn ref) (kn cs) s).
  (* a variable the rename [m] leaves where it is without a collision: below [gb], moved by [m],
     or neither a target nor above every target *)
  Definition rn_keep (m : list (nat * nat)) (top v : nat) : bool :=
    (Nat.ltb v gb || existsb (fun q => Nat.eqb (fst q) v) m || (negb (vs_tgt v m) && Nat.leb v top))%bool.
  Fixpoint rn_ixs_from (m : list (nat * nat)) (top i : nat) (k : list kentry) : list nat :=
    match k with
    | [] => []
    | K :: r => if kvars_all (rn_keep m top) K then rn_ixs_from m top (S i) r else i :: rn_ixs_from m top (S i) r
    end.
  Definition rn_ixs (m : list (nat * nat)) (k : list kentry) : list nat :=
    rn_ixs_from m (fold_left Nat.max (map snd m) 0%nat) 0 k.
End Unify.

(* The hand-off the collector stops at to read the state at the step. *)
Definition HCUT : nat := 990.
(* [rn_step gb ref H k]: in place of the step before [k], once the collector has the state at it
   ([H HCUT]), a forget of the facts the rename cannot carry and the rename onto [ref]'s
   numbering; until then, the hand-off [HCUT]. *)
Definition rn_step (gb : nat) (ref : acs) (H : nat -> option acs) (k : plan) : plan :=
  match H HCUT with
  | Some pre => let m := vunify gb pre ref in PForget (rn_ixs gb m (kn pre)) (PRename m k)
  | None => PHandoff HCUT
  end.
(* [p] with each [PCompact k] replaced by [w k] *)
Fixpoint on_compact (w : plan -> plan) (p : plan) : plan :=
  match p with
  | PRun stops k => PRun stops (on_compact w k)
  | PSplit e mid k1 k2 => PSplit e mid (on_compact w k1) (on_compact w k2)
  | PCase2 e mid k1 k2 => PCase2 e mid (on_compact w k1) (on_compact w k2)
  | PCaseDisj b1 b2 k1 k2 => PCaseDisj b1 b2 (on_compact w k1) (on_compact w k2)
  | PShDisj b1 n1 b2 n2 k => PShDisj b1 n1 b2 n2 (on_compact w k)
  | PContra => PContra
  | PFact K k => PFact K (on_compact w k)
  | PJoin b off n k => PJoin b off n (on_compact w k)
  | PForget ixs k => PForget ixs (on_compact w k)
  | PDropRange b n k => PDropRange b n (on_compact w k)
  | PGcKeep ws k => PGcKeep ws (on_compact w k)
  | PBump m k => PBump m (on_compact w k)
  | PHavoc rs k => PHavoc rs (on_compact w k)
  | PHavocBig K k => PHavocBig K (on_compact w k)
  | PFresh r logc base k => PFresh r logc base (on_compact w k)
  | PSys y k => PSys y (on_compact w k)
  | PMmap ka kb => PMmap (on_compact w ka) (on_compact w kb)
  | PMmapIn a b c => PMmapIn (on_compact w a) (on_compact w b) (on_compact w c)
  | PMprotect a b => PMprotect (on_compact w a) (on_compact w b)
  | PBrk2 a b => PBrk2 (on_compact w a) (on_compact w b)
  | PX x args k => PX x args (on_compact w k)
  | PExt id args k => PExt id args (on_compact w k)
  | PEmit id args k => PEmit id args (on_compact w k)
  | PExt2 id args k1 k2 => PExt2 id args (on_compact w k1) (on_compact w k2)
  | PLoop J N inv body k => PLoop J N inv (on_compact w body) (on_compact w k)
  | PNext => PNext
  | PHandoff h => PHandoff h
  | PExit => PExit
  | PSpin => PSpin
  | PFog i sz k => PFog i sz (on_compact w k)
  | PFogNew i sz k => PFogNew i sz (on_compact w k)
  | PGhost b n k => PGhost b n (on_compact w k)
  | PUnvis b n k => PUnvis b n (on_compact w k)
  | PHavocBrk lo hi k => PHavocBrk lo hi (on_compact w k)
  | PIntro lo hi k => PIntro lo hi (on_compact w k)
  | PDiamond joinpc rs k => PDiamond joinpc rs (on_compact w k)
  | PRename m k => PRename m (on_compact w k)
  | PCompact k => w (on_compact w k)
  | PVia j js lo karms k => PVia j js lo (on_compact w karms) (on_compact w k)
  | PMerge j => PMerge j
  | PAbstractCell b n k => PAbstractCell b n (on_compact w k)
  | PHavocWords bs k => PHavocWords bs (on_compact w k)
  | PRespell r e k => PRespell r e (on_compact w k)
  | PMmapInH a b c => PMmapInH (on_compact w a) (on_compact w b) (on_compact w c)
  | PBrkU a b => PBrkU (on_compact w a) (on_compact w b)
  | PDisjDia b1 b2 o2 joinpc rs k => PDisjDia b1 b2 o2 joinpc rs (on_compact w k)
  | PWordFresh b n k => PWordFresh b n (on_compact w k)
  | PCaseDisjO b1 b2 o k1 k2 => PCaseDisjO b1 b2 o (on_compact w k1) (on_compact w k2)
  end.
(* [p] with its leading [PRename m k] replaced by [w k] *)
Definition on_rename0 (w : plan -> plan) (p : plan) : plan :=
  match p with PRename _ k => w k | _ => p end.
(* the recorded state after its plan's recorded first rename [m]: the reference of a node whose
   plan starts with that rename *)
Definition rn_rec (gb : nat) (cs : acs) (m : list (nat * nat)) : acs :=
  match node_rename gb cs m with Some x => x | None => cs end.

(* 6. A via's arms before its continuation.  [collect_hjl] makes a [PVia]'s join state the state
   of the first arm that reaches its [PMerge], and since [check] runs a via's continuation before
   its arms, the next run checks the continuation from that one arm's state, its own split facts
   included.  In SROOM [a], via 0's first arm is the one whose
   length field is 0, so the driver loop's count is 0 in the continuation, the run leaves the
   loop and calls [free], and via 1's join comes back inside [free]'s [memset] (406464, the
   stack 2176 bytes deeper) where the recorded join, made from every arm, is at 523784.
   [collect_hjla] merges every arm first.  A via that has a join state and is not yet settled
   ([SV]) has its continuation deferred to the hand-off [HK0 + j] ([pjs]'s [D]), whose state is
   the join itself ([hk_ext]), so a run checks the via's arms against the join and goes no
   further; a refused arm is joined in as [collect_hjl] does.  When a run ends with nothing left
   to join, every via with a join state is settled and the next run checks the continuations.
   The last run defers nothing it reaches, so it is the check of the certificate's plan. *)
Definition hk_ext (J H : nat -> option acs) (h : nat) : option acs :=
  if (Nat.leb HK0 h && Nat.ltb h HCUT)%bool then J (h - HK0)%nat else H h.
Fixpoint collect_hjla (A : atable) (fuel : nat)
    (run : (nat -> option acs) -> (nat -> option acs) -> (nat -> option acs) -> (nat -> bool) -> cres)
    (H J L : list (nat * acs)) (RJ SV : list nat) : list (nat * acs) * list (nat * acs) * list (nat * acs) * option cres :=
  match fuel with
  | O => (H, J, L, None)
  | S f =>
      let r := run (hlookup H) (hlookup J) (hlookup L) (fun j => negb (existsb (Nat.eqb j) SV)) in
      let settle := fun _ : unit =>
        match filter (fun j => negb (existsb (Nat.eqb j) SV)) (map fst J) with
        | [] => (H, J, L, Some r)
        | U => collect_hjla A f run [] J L RJ (U ++ SV)
        end in
      match r with
      | CErr code (PHandoff h) cs =>
          if Z.eqb code 4%Z then collect_hjla A f run (hupd h cs H) J L RJ SV
          else if Z.eqb code 3%Z then
            match hlookup H h with
            | Some a => collect_hjla A f run (hupd h (join_states a cs) H) J L RJ SV
            | None => settle tt
            end
          else settle tt
      | CErr code (PMerge j) cs =>
          if Z.eqb code 3%Z then
            let js := match hlookup J j with
                      | Some a => if existsb (Nat.eqb j) RJ then join_states_h A a cs else cs
                      | None => cs
                      end in
            collect_hjla A f run [] (hupd j js J) L (j :: RJ) SV
          else settle tt
      | CErr code (PLoop J0 _ inv _ _) cs =>
          if Z.eqb code 3%Z then collect_hjla A f run [] J (hupd J0 (loop_weaken A J0 inv cs) L) RJ SV
          else settle tt
      | _ => settle tt
      end
  end.
