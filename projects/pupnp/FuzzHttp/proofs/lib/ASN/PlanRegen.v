(* SPDX-License-Identifier: MIT *)
(* Made from spirv-tools/spvtools_binary_parser_fuzzer's AsPlanRegen.v and double-conversion/
   string_to_double_fuzzer's PlanRegen.v, over this unit's plan and state types (AsanPlan.plan,
   AsanPlanCore.acs).

   1. [psh f]: a recorded plan's variable renumbering, as a total function applied where the plan
   is checked, so a recorded plan is not rewritten by hand.  LPS 727298f3 gives the launch more
   plan variables ([V_G], [V_GID]: NX0 11 -> 13) and more of the auxv to read, so the runs
   allocate their fresh variables at other numbers than the runs the recorded plans were written
   against.  The map is read off the new run (a probe that stops the run where the plan names a
   variable and prints the state), never chosen.  It starts at the lowest fresh variable the
   recorded plans name (double-conversion's [SU_TBL] form): the plans also name the launch
   layout through definitions over the NEW launch variables ([e_atr8] names [V_G]), and those
   must not move.

   WHICH plan fields are variables, read from [AsanPlan.check]'s arms: PBump m, PLoop J,
   PRename m (both sides), PVia lo; every embedded expr, kentry and state.  Every other nat
   field stays: registers, widths, list indices, ids, counts, size thresholds.
   SOUNDNESS DOES NOT REST ON THIS CLASSIFICATION: a certificate vm_computes through [psh] and
   re-checks the shifted plan; a wrong map or classification can only make a certificate red.

   2. The states a run hands off, computed from the run ([collect_k]), and the maps the
   certificates check against ([hs1], [hs2]). *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AxSymExec3 AsanPlanCore AsanPlan.
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
  Definition sesh (s : sentry) : sentry := SE (sash (e_addr s)) (e_width s) (esh (e_val s)).
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
    | PMmapIn ka kb kc => PMmapIn (psh ka) (psh kb) (psh kc)
    | PMprotect ka kb => PMprotect (psh ka) (psh kb)
    | PBrk2 ka kb => PBrk2 (psh ka) (psh kb)
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
    | PMmapInH ka kb kc => PMmapInH (psh ka) (psh kb) (psh kc)
    end.
End Shift.

(* the renumbering every map here has: the identity below [t], then [+ d] *)
Definition vshift (t d : nat) (v : nat) : nat := if Nat.ltb v t then v else (v + d)%nat.

(* a total monotone map given as a table read from a probe: ascending thresholds [(t, d)] in the
   OLD numbering, an old variable [v] moves by the [d] of the last [t <= v] (by 0 below the first) *)
Fixpoint tbl_d (tbl : list (nat * nat)) (v acc : nat) : nat :=
  match tbl with [] => acc | (t, d) :: r => if Nat.leb t v then tbl_d r v d else acc end.
Definition tshift (tbl : list (nat * nat)) (v : nat) : nat := (v + tbl_d tbl v 0)%nat.

(* The states a run hands off, computed from the run.  [check]'s [PHandoff h] arm returns
   [CErr 4 (PHandoff h) cs] when its handoff map has no state for [h], and
   [CErr 3 (PHandoff h) cs] when the reached [cs] does not entail the state it has; [cs] is then
   the state at that handoff.  [collect_k] reruns the check: a missing state becomes the reached
   one, and a state some other path (or the other CONFIG_RSEQ value) does not entail becomes the
   join of the two.  A state computed this way is a definition, not an assumption: the
   certificate that names it re-runs the check, which must entail it. *)

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

(* [run hs] is the certificate's own check with handoff map [hs].  [key h] is the entry hand-off
   [h] reads and writes: the identity, or a map that sends hand-offs the certificate gives one
   state to one entry. *)
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

(* several runs against one map (the CONFIG_RSEQ values, or a segment's start states): the map
   one run leaves is where the next starts, until none moves it *)
Fixpoint collect_runs (key : nat -> nat) (fuel : nat) (runs : list ((nat -> option acs) -> cres)) (m : list (nat * acs)) : list (nat * acs) :=
  match fuel with
  | O => m
  | S f => collect_runs key f runs (fold_left (fun m0 run => collect_k key 20 run m0) runs m)
  end.

(* a collected map's state at [h] ([d] when the run never reached [h]: a certificate that reads it
   then fails visibly) *)
Definition hget (m : list (nat * acs)) (h : nat) (d : acs) : acs :=
  match hlookup m h with Some a => a | None => d end.

(* the hand-off maps the certificates check against: one state at one hand-off, or two *)
Definition hs1 (k : nat) (s : acs) (h : nat) : option acs := if Nat.eqb h k then Some s else None.
Definition hs2 (k1 : nat) (s1 : acs) (k2 : nat) (s2 : acs) (h : nat) : option acs :=
  if Nat.eqb h k1 then Some s1 else if Nat.eqb h k2 then Some s2 else None.

Lemma hs1_some : forall k s h ch, hs1 k s h = Some ch -> ch = s.
Proof.
  intros k s h ch H. unfold hs1 in H. destruct (Nat.eqb h k); [injection H as E; symmetry; exact E| discriminate H].
Qed.
Lemma hs2_some : forall k1 s1 k2 s2 h ch, hs2 k1 s1 k2 s2 h = Some ch -> ch = s1 \/ ch = s2.
Proof.
  intros k1 s1 k2 s2 h ch H. unfold hs2 in H.
  destruct (Nat.eqb h k1); [injection H as E; left; symmetry; exact E|].
  destruct (Nat.eqb h k2); [injection H as E; right; symmetry; exact E| discriminate H].
Qed.

(* the shape a check returns ([SNil], which no chain accepts, on an error) *)
Definition sh_of (r : cres) : shape := match r with COk s => s | CErr _ _ _ => SNil end.
