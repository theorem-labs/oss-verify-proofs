(* SPDX-License-Identifier: MIT *)
(* Made from boost-beast/http_request's As/AsPlanRegen.v (itself made from spirv-tools/spvtools_binary_parser_fuzzer's
   bpA/Start/AsPlanRegen.v, the renumbering, and double-conversion/string_to_double_fuzzer's PlanRegen.v, the
   hand-off collection, both made from jsoncons/fuzz_bigint's PlanRegenK.v), over this unit's AsanPlan.plan and
   AsanPlanCore.acs (the same 48 plan constructors and the same state fields).  Shared by the ASan (AsCert) and the
   ASan+UBSan (Both/AsCert) start-up data.

   1. [psh f]: a recorded plan's variable renumbering, as a total function applied where the plan is
   checked, so a recorded plan is not rewritten by hand.  LPS 727298f3 gives the launch more plan
   variables ([V_G], [V_R] and [V_GID]: NX0 11 -> 14) and more of the auxv to read, so the runs allocate their
   fresh variables at other numbers than the runs the recorded plans were written against.  The map is
   read off the new run (a probe that stops the run where the plan names a variable and prints the
   state), never chosen.

   WHICH plan fields are variables, read from [AsanPlan.check]'s arms: PBump m, PLoop J, PRename m (both
   sides), PVia lo, PRangeGaps v, PCaseGaps v; every embedded expr, kentry, hull and state.  Every other
   nat field stays: registers, widths, list indices, ids, counts.
   SOUNDNESS DOES NOT REST ON THIS CLASSIFICATION: a certificate vm_computes through [psh] and re-checks
   the shifted plan; a wrong map or classification can only make a certificate red.

   2. The states a run hands off, computed from the run ([collect_k], [collect_runs]): [check]'s
   [PHandoff h] arm returns [CErr 4 (PHandoff h) cs] when its hand-off map has no state for [h] and
   [CErr 3 (PHandoff h) cs] when the reached [cs] does not entail the state it has.  A missing state
   becomes the reached one (its write log emptied: [entails] accepts only a hand-off state with an empty
   log, and does not read the reached state's), and a state another run (the other CONFIG_RSEQ value, or
   another branch) does not entail becomes the join of the two.  A state computed this way is a
   definition, not an assumption: the certificate that names it re-runs the check, which must entail
   it. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AsanPlanCore AsanPlan.
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
  Definition hsh (h : hull) : hull := (esh (fst h), snd h).
  Definition amsh (m : amap) : amap := AM (esh (am_base m)) (esh (am_len m)) (am_kind m).
  Definition fdsh (d : afd) : afd :=
    match d with FdFile k len off => FdFile k (esh len) (esh off) | _ => d end.
  Definition sesh (s : sentry) : sentry := SE (sash (e_addr s)) (e_width s) (esh (e_val s)).
  (* a state's renumbering; its fresh counter moves with the map *)
  Definition ash (cs : acs) : acs :=
    let ss := a_ss cs in
    ACS (SSR (s_pc ss) (map esh (s_regs ss)) (map sesh (s_log ss)) (map ksh (s_know ss)) (f (s_next ss))
             (option_map sash (s_resv ss)))
        (map amsh (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs) (map pesh (a_vis cs))
        (map pesh (a_ghost cs)) (a_abytes cs) (esh (a_brk cs)) (fdsh (a_fd cs)) (a_tidset cs)
        (map (vmop_map esh) (a_vmops cs)).

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
    | PMmap1 k => PMmap1 (psh k)
    | PMmapIn1 k => PMmapIn1 (psh k)
    | PMprotect1 k => PMprotect1 (psh k)
    | PBrk2 k1 k2 => PBrk2 (psh k1) (psh k2)
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
    | PNameCell b n k => PNameCell (esh b) n (psh k)
    | PCaseGaps v sc ks => PCaseGaps (f v) sc (map psh ks)
    | PRangeGaps v sc k => PRangeGaps (f v) sc (psh k)
    | PMmapGaps ks => PMmapGaps (map psh ks)
    | PFrozen id hs ws cold items k => PFrozen id (map hsh hs) (map hsh ws) (map esh cold) items (psh k)
    end.
End Shift.

(** the step map: variables at or above [b] move up by [d]; the launch variables below [b] stay *)
Definition vshift (b d : nat) (v : nat) : nat := if Nat.ltb v b then v else (v + d)%nat.

(** a total monotone map given as a table read from a probe: ascending thresholds [(t, d)] in the OLD
    numbering, an old variable [v] moves by the [d] of the last [t <= v] (by 0 below the first) *)
Fixpoint tbl_d (tbl : list (nat * nat)) (v acc : nat) : nat :=
  match tbl with [] => acc | (t, d) :: r => if Nat.leb t v then tbl_d r v d else acc end.
Definition tshift (tbl : list (nat * nat)) (v : nat) : nat := (v + tbl_d tbl v 0)%nat.

(** The join of two states at one hand-off.  [AsanPlanCore.entails] (its knowledge test [kn_incl_cur] is
    membership, [kn_incl_cur_eq]) needs equal registers, mappings,
    visibility, ghosts, brk, fd, tid flag and vm operations, a subset of the knowledge, and bounds on four
    sizes; so the join is the first state with the knowledge both have (the hand-off's own test on one
    fact, [kentry_eqb]) and the four sizes at their weaker ends, its log empty. *)
Definition join_states (a b : acs) : acs :=
  let ss := a_ss a in
  ACS (SSR (s_pc ss) (s_regs ss) [] (filter (fun K => existsb (kentry_eqb K) (kn b)) (kn a))
           (Nat.max (nxt a) (nxt b)) (s_resv ss))
      (a_maps a) (Z.max (a_totsz a) (a_totsz b)) (Z.min (a_ylo a) (a_ylo b))
      (Z.max (a_eager a) (a_eager b)) (a_vis a) (a_ghost a) (Z.max (a_abytes a) (a_abytes b))
      (a_brk a) (a_fd a) (a_tidset a) (a_vmops a).

(** a reached state as a hand-off state: its write log emptied *)
Definition hclean (c : acs) : acs :=
  let ss := a_ss c in
  ACS (SSR (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss) (s_resv ss)) (a_maps c) (a_totsz c) (a_ylo c)
      (a_eager c) (a_vis c) (a_ghost c) (a_abytes c) (a_brk c) (a_fd c) (a_tidset c) (a_vmops c).

Definition hlookup (m : list (nat * acs)) (h : nat) : option acs :=
  match find (fun q => Nat.eqb (fst q) h) m with Some q => Some (snd q) | None => None end.
Definition hupd (h : nat) (a : acs) (m : list (nat * acs)) : list (nat * acs) :=
  (h, a) :: filter (fun q => negb (Nat.eqb (fst q) h)) m.
Definition hstate (m : list (nat * acs)) (dflt : acs) (h : nat) : acs :=
  match hlookup m h with Some a => a | None => dflt end.

(** [run js] is a certificate's own check with hand-off map [js]. *)
Fixpoint collect_k (fuel : nat) (run : (nat -> option acs) -> cres) (m : list (nat * acs)) : list (nat * acs) :=
  match fuel with
  | O => m
  | S f =>
      match run (hlookup m) with
      | CErr code (PHandoff h) cs =>
          if Z.eqb code 4%Z then collect_k f run (hupd h (hclean cs) m)
          else if Z.eqb code 3%Z then
            match hlookup m h with
            | Some a => collect_k f run (hupd h (join_states a cs) m)
            | None => m
            end
          else m
      | _ => m
      end
  end.

(** several runs against one map (the CONFIG_RSEQ values, or a level's start states): the map one run
    leaves is where the next starts, until none moves it *)
Fixpoint collect_runs (fuel : nat) (runs : list ((nat -> option acs) -> cres)) (m : list (nat * acs)) : list (nat * acs) :=
  match fuel with
  | O => m
  | S f => collect_runs f runs (fold_left (fun m0 run => collect_k 20 run m0) runs m)
  end.

(** 3. A recorded state that no run reaches as a hand-off, in the new launch layout: OSSV-509's fixed rule
    (its run record, "Hand-off states filtered by a fixed rule", addition of 2026-11-13T07:05Z),
    [relaunch D L (ash hand_f S)], here as ONE function of the states it is computed from:
    [relaunch carried S0 S1 E], where [E] is the recorded end state and [S0] the recorded start state, both
    renumbered by the probe-read map, and [S1] the computed start state (the run's own).
    - D: the facts of [E] that [S0] holds and [S1] lacks (carried from the old launch layout), dropped;
    - L: the facts of [S1] that [S0] lacks and the consumer's own test [carried] accepts, added;
    - the four size bounds of [E] move by the computed start's against the recorded start's.
    The form of double-conversion/string_to_double_fuzzer's PlanRegen.v [relaunch], with one difference: a
    [D] fact is DROPPED, not replaced in place by a fact that holds in every state, because this unit's
    hole certificates (Common/Br/Br3Trans.v [leaf3b_chk], Br3Know.v [know3_entry_chk2]) accept an end-state
    fact only as the start's own, as one the run writes, or as a range/disjointness fact on a variable, and
    a fact on no variable is none of these; nothing reads an end state's facts by index (its consumers test
    membership).  Every kept or added fact and every bound is checked again by the certificate that names the
    state, so a wrong [D], [L] or bound can only fail the build. *)
Definition kin (K : kentry) (l : list kentry) : bool := existsb (kentry_eqb K) l.
Definition relaunch_D (S0 S1 E : acs) : list kentry :=
  filter (fun K => (kin K (kn S0) && negb (kin K (kn S1)))%bool) (kn E).
Definition relaunch_L (carried : list kentry -> list kentry) (S0 S1 : acs) : list kentry :=
  carried (filter (fun K => negb (kin K (kn S0))) (kn S1)).
Definition relaunch (carried : list kentry -> list kentry) (S0 S1 E : acs) : acs :=
  let D := relaunch_D S0 S1 E in
  let L := relaunch_L carried S0 S1 in
  let ss := a_ss E in
  let k := filter (fun K => negb (kin K D)) (s_know ss) in
  ACS (SSR (s_pc ss) (s_regs ss) (s_log ss) (k ++ filter (fun K => negb (kin K k)) L) (s_next ss) (s_resv ss))
      (a_maps E) (a_totsz E + (a_totsz S1 - a_totsz S0))%Z (a_ylo E + (a_ylo S1 - a_ylo S0))%Z
      (a_eager E + (a_eager S1 - a_eager S0))%Z (a_vis E) (a_ghost E) (a_abytes E + (a_abytes S1 - a_abytes S0))%Z
      (a_brk E) (a_fd E) (a_tidset E) (a_vmops E).
