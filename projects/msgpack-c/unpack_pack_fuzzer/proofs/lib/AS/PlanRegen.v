(* SPDX-License-Identifier: MIT *)
(* Regenerating the start-up certificates' data in the build rather than by hand (LPS 727298f3):
   a plan's variable renumbering, and the states a run hands off.  Copied from
   projects/zstd/fse_read_ncount/proofs/lib/AS/PlanRegen.v (the same plan type), which was copied
   for that plan type from projects/jsoncons/fuzz_bigint/proofs/lib/PlanRegenK.v; [hvisit] and
   [collect_handoffs1] from projects/reac-pw/fuzz_headamp/proofs/lib/Reusable/PlanRegen.v. *)
(*

   1. [psh f]: a plan's variable renumbering, as a total function applied where the plan is
   checked, so a recorded plan is not rewritten by hand.  LPS 727298f3 gives the launch more plan
   variables ([V_GID], NX0 12 -> 13; [V_G] before it) and more of the auxv to read, so the start-up
   run allocates its fresh variables at other numbers than the run the recorded plans were written
   against.  The map for each plan is read off the new run (a probe that stops the run where the
   plan names the variable and prints the state), never chosen, and passed to [psh] as [f].

   Which plan fields are variables, read from this unit's [check] (AsanPlan.v): PBump m, PLoop J,
   PRename m (both sides), PVia lo, and every embedded expr and kentry.  Every other nat field
   stays: registers (PHavoc, PFresh, PDiamond, PRespell), list indices (PForget, PFog, PFogNew),
   ids (PExt, PEmit, PExt2, PHandoff, PMerge, PVia j), counts (PJoin, PHavocBig).  The embedded
   states of PLoop and PVia are not shifted.  Soundness does not rest on this classification: the
   certificates compute through [psh] and re-check the shifted plan; a wrong map can only make a
   certificate fail. *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import APC. Import AP.

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
    end.
End Shift.

(* 1b. [pmapH h]: replace the first node, on every path, at which [h] answers [Some q] by [q] (the
   rest of the plan unchanged).  Used to change one recorded node chain by a fixed rule computed in
   the build (segB's AT_RANDOM split chain, AsanStartupCertC.v); the certificate re-checks the
   result.  The traversal of zstd/fse_read_ncount's probe helpers (ZZ_tools.v). *)
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

(* The maps [psh] is given: breakpoints (old, new), ascending in old, each read from a probe run
   (the run cut where the plan names the variable); the last breakpoint at or below [v] moves [v]
   by [new - old], and below the first one [v] stays (the launch's own variables). *)
Definition mapf (bps : list (nat * nat)) (v : nat) : nat :=
  fold_left (fun acc (q : nat * nat) => if Nat.leb (fst q) v then (v - fst q + snd q)%nat else acc) bps v.

(* 2. The states a run hands off, computed from the run.  [check]'s [PHandoff h] arm (AsanPlan.v)
   returns [CErr 4 (PHandoff h) cs] when its hand-off map has no state for [h], and
   [CErr 3 (PHandoff h) cs] when the reached [cs] does not entail the state it has; [cs] is then
   the state at that hand-off.  [collect_handoffs] reruns the check: a missing state becomes the
   reached one, and a state another path does not entail becomes the join of the two.  A state
   computed this way is a definition, not an assumption: the certificate that names it re-runs the
   check, which must entail it.  [join_states] keeps the first state with the knowledge both have
   and the looser of each size bound (this unit's [entails] tests the knowledge as a plain subset
   and compares the four bounds; it has no [kpriv_geb]).  [collect_handoffs1] makes the same map
   from one run of the check instead of one run per state it adds (below). *)
Definition join_states (a b : acs) : acs :=
  let a1 := set_kn a (filter (fun K => existsb (kentry_eqb K) (kn b)) (kn a)) in
  let ss := a_ss a1 in
  let a2 := with_ss a1 (mk_ss (s_pc ss) (s_regs ss) (s_know ss) (Nat.max (nxt a) (nxt b))) in
  ACS (a_ss a2) (a_maps a2) (Z.max (a_totsz a) (a_totsz b)) (Z.min (a_ylo a) (a_ylo b))
      (Z.max (a_eager a) (a_eager b)) (a_vis a2) (a_ghost a2) (Z.max (a_abytes a) (a_abytes b))
      (a_brk a2) (a_fd a2) (a_tidset a2).

Definition hlookup (m : list (nat * acs)) (h : nat) : option acs :=
  match find (fun q => Nat.eqb (fst q) h) m with Some q => Some (snd q) | None => None end.
Definition hupd (h : nat) (a : acs) (m : list (nat * acs)) : list (nat * acs) :=
  (h, a) :: filter (fun q => negb (Nat.eqb (fst q) h)) m.

(* [run js] is the certificate's own check with hand-off map [js]. *)
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
   run per state it adds.  [crun] is the certificate's own check written as [check_coll]
   (AsanPlan.v) with [hvisit] at its hand-offs, started from [(fuel, m)].
   Why one run gives the same map: [check] reads its map only at [PHandoff h], a leaf, so the
   hand-offs a run reaches, in order, and the state at each, do not depend on the map until the
   run stops at one.  A hand-off a run has passed is passed again by the next run: only the state
   at the [h] just changed is new, and a state that entails [a] entails [join_states a b] (this
   unit's [join_states] keeps [a]'s pc, registers, mappings, visibility, ghost cells, brk, fd and
   tid flag, a part of its knowledge, an empty log, and the looser of the four bounds [entails]
   compares).  So [collect_handoffs]'s runs make their changes at the hand-offs in the order the
   run reaches them, and [hvisit] makes, at the hand-off reached, the changes they make there,
   one per unit of fuel, until the map entails the reached state; then the run goes on.  With the
   fuel spent it changes nothing more, as [collect_handoffs] stops.  The list is
   [collect_handoffs fuel run m]'s at the same fuel, in the same order (on
   reac-pw/fuzz_headamp, computed equal on its two start-up runs at both CONFIG_RSEQ flags). *)
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
Definition collect_handoffs1 (fuel : nat) (crun : nat * list (nat * acs) -> cres * (nat * list (nat * acs)))
  (m : list (nat * acs)) : list (nat * acs) :=
  snd (snd (crun (fuel, m))).
(* the state at hand-off [h], or [dflt] when the run never reaches it *)
Definition hstate (m : list (nat * acs)) (dflt : acs) (h : nat) : acs :=
  match hlookup m h with Some a => a | None => dflt end.

(* What a computed table says, read off its keys (a [vm_compute] of [map fst m]): a table with the
   one key [h0] answers only at [h0], with [hstate m d h0]; a table with two different keys
   answers only at those two. *)
Lemma hlookup_one : forall m d h0, map fst m = [h0] ->
  forall h ch, hlookup m h = Some ch -> h = h0 /\ ch = hstate m d h0.
Proof.
  intros [|[k a] [|q m]] d h0 Hk h ch Hh; cbn in Hk; try discriminate. injection Hk as ->.
  unfold hstate, hlookup in *. simpl in *. rewrite Nat.eqb_refl.
  destruct (Nat.eqb h0 h) eqn:E; simpl in Hh; [| discriminate].
  apply Nat.eqb_eq in E. injection Hh as <-. split; [symmetry; exact E| reflexivity].
Qed.
Lemma hlookup_two : forall m d h1 h2, map fst m = [h1; h2] -> Nat.eqb h1 h2 = false ->
  forall h ch, hlookup m h = Some ch ->
  (h = h1 /\ ch = hstate m d h1) \/ (h = h2 /\ ch = hstate m d h2).
Proof.
  intros [|[k1 a1] [|[k2 a2] [|q m]]] d h1 h2 Hk H12 h ch Hh; cbn in Hk; try discriminate.
  injection Hk as -> ->. unfold hstate, hlookup in *. simpl in *.
  rewrite H12, !Nat.eqb_refl.
  destruct (Nat.eqb h1 h) eqn:E1; simpl in Hh.
  - apply Nat.eqb_eq in E1. injection Hh as <-. left. split; [symmetry; exact E1| reflexivity].
  - destruct (Nat.eqb h2 h) eqn:E2; simpl in Hh; [| discriminate].
    apply Nat.eqb_eq in E2. injection Hh as <-. right. split; [symmetry; exact E2| reflexivity].
Qed.
(* the same, whichever order the run reached the two hand-offs in *)
Lemma hlookup_two_any : forall m d h1 h2, (map fst m = [h1; h2] \/ map fst m = [h2; h1]) -> Nat.eqb h1 h2 = false ->
  forall h ch, hlookup m h = Some ch ->
  (h = h1 /\ ch = hstate m d h1) \/ (h = h2 /\ ch = hstate m d h2).
Proof.
  intros m d h1 h2 [Hk|Hk] H12 h ch Hh.
  - exact (hlookup_two m d h1 h2 Hk H12 h ch Hh).
  - rewrite Nat.eqb_sym in H12.
    destruct (hlookup_two m d h2 h1 Hk H12 h ch Hh) as [H|H]; [right|left]; exact H.
Qed.
