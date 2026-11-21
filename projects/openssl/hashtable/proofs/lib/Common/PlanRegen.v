(* SPDX-License-Identifier: MIT *)
(* Made from double-conversion/string_to_double_fuzzer's PlanRegen.v (its 727298f3 start-up
   certificate regeneration), over this unit's plan and state types.

   Regenerating start-up certificate data in the build rather than by hand, at LPS 727298f3:

   1. [psh f]: a plan's variable renumbering, as a total function applied where the plan is
      checked, so a recorded plan is not rewritten by hand.  The revision gives the launch more
      plan variables ([V_R], [V_GID]: NX0 13 -> 15) and more of the auxv to read, so the runs
      allocate their fresh variables at other numbers than the runs the recorded plans were written
      against.  The map is read off the new run (a probe that stops the run where the plan names a
      variable and prints the state), never chosen.  Which plan fields are variables is read from
      [CAP.check]'s arms: PBump m, PLoop J, PRename (both sides), PVia lo, PBand v, the band-diamond
      extern's band variable ([xash]), and every embedded expression and fact.  Registers, list
      indices, ids, counts and fuel stay.
      Soundness does not rest on this classification: the certificates compute through [psh] and
      re-check the renumbered plan, so a wrong map can only make a certificate fail.

   2. [collect_handoffs]: the states a run hands off, computed by rerunning the certificate's own
      check, starting from the empty table (a hand-off the table lacks, [CErr 4], records the
      reached state; one the reached state does not imply, [CErr 3], joins the two).  A computed
      state is a definition that the certificate re-checks, never an assumption. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan.
Import ListNotations. Import AX2. Import APC. Import CAP.

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
  (* a state's renumbering; its fresh counter moves with the map *)
  Definition ash (cs : acs) : acs :=
    let ss := a_ss cs in
    ACS (SSR (s_pc ss) (map esh (s_regs ss)) (s_log ss) (map ksh (s_know ss)) (f (s_next ss))
             (option_map sash (s_resv ss)))
        (map amsh (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs) (map pesh (a_vis cs))
        (map pesh (a_ghost cs)) (a_abytes cs) (esh (a_brk cs)) (fdsh (a_fd cs)) (a_tidset cs).

  (* an extern's arguments; the band-diamond extern (id 42 of HACheckG/HBCheckG) names its band
     variable by its first argument, a literal (0: the one register a0 names, read in the run) *)
  Definition xash (id : nat) (args : list expr) : list expr :=
    match args with
    | ELit v :: r =>
        if (Nat.eqb id 42 && Z.ltb 0%Z v)%bool then ELit (Z.of_nat (f (Z.to_nat v))) :: map esh r
        else map esh args
    | _ => map esh args
    end.

  (* [pshs sf kc kf]: the renumbering of a plan whose embedded states (loop invariants, [PVia]
     states) are mapped by [sf]; after a [PCompact] the rest is mapped by [g] when [kc = Some g] (a
     compaction renumbers); [psh] maps embedded states by [ash].  [kf]: keep the plan's [PForget]
     nodes.  They are lists of knowledge INDICES into the old run's state; where the new run's list
     of facts differs from the old one's, an index can name another fact than the one the old run
     dropped.  A [PForget] only weakens a state, so a plan checked without them is checked as
     soundly ([kf = false]); a compaction may need the dropped facts gone, so a certificate checks
     the plan with them first and without them when that fails (double-conversion/
     string_to_double_fuzzer's [mplan]/[mplanD]). *)
  Section Plans.
  Variable sf : acs -> acs.
  Variable kc : option (plan -> plan).
  Variable kf : bool.
  Fixpoint pshs_go (p : plan) : plan :=
    match p with
    | PRun stops k => PRun stops (pshs_go k)
    | PSplit e mid k1 k2 => PSplit (esh e) mid (pshs_go k1) (pshs_go k2)
    | PCase2 e mid k1 k2 => PCase2 (esh e) mid (pshs_go k1) (pshs_go k2)
    | PCaseDisj b1 b2 k1 k2 => PCaseDisj (esh b1) (esh b2) (pshs_go k1) (pshs_go k2)
    | PShDisj b1 n1 b2 n2 k => PShDisj (esh b1) (esh n1) (esh b2) (esh n2) (pshs_go k)
    | PContra => PContra
    | PFact K k => PFact (ksh K) (pshs_go k)
    | PJoin b off n k => PJoin (esh b) off n (pshs_go k)
    | PForget ixs k => if kf then PForget ixs (pshs_go k) else pshs_go k
    | PDropRange b n k => PDropRange (esh b) (esh n) (pshs_go k)
    | PGcKeep ws k => PGcKeep (map pesh ws) (pshs_go k)
    | PBump m k => PBump (f m) (pshs_go k)
    | PHavoc rs k => PHavoc rs (pshs_go k)
    | PHavocBig K k => PHavocBig K (pshs_go k)
    | PFresh r logc base k => PFresh r logc (option_map esh base) (pshs_go k)
    | PSys y k => PSys y (pshs_go k)
    | PMmap ka kb => PMmap (pshs_go ka) (pshs_go kb)
    | PMmapIn a b c => PMmapIn (pshs_go a) (pshs_go b) (pshs_go c)
    | PMprotect a b => PMprotect (pshs_go a) (pshs_go b)
    | PBrk2 a b => PBrk2 (pshs_go a) (pshs_go b)
    | PX x args k => PX x (map esh args) (pshs_go k)
    | PExt id args k => PExt id (xash id args) (pshs_go k)
    | PEmit id args k => PEmit id (map esh args) (pshs_go k)
    | PExt2 id args k1 k2 => PExt2 id (map esh args) (pshs_go k1) (pshs_go k2)
    | PLoop J N inv body k => PLoop (f J) (esh N) (sf inv) (pshs_go body) (pshs_go k)
    | PNext => PNext
    | PHandoff h => PHandoff h
    | PExit => PExit
    | PSpin => PSpin
    | PFog i sz k => PFog i sz (pshs_go k)
    | PFogNew i sz k => PFogNew i sz (pshs_go k)
    | PGhost b n k => PGhost (esh b) (esh n) (pshs_go k)
    | PUnvis b n k => PUnvis (esh b) (esh n) (pshs_go k)
    | PHavocBrk lo hi k => PHavocBrk lo hi (pshs_go k)
    | PIntro lo hi k => PIntro lo hi (pshs_go k)
    | PDiamond joinpc rs k => PDiamond joinpc rs (pshs_go k)
    | PRename m k => PRename (map (fun q => (f (fst q), f (snd q))) m) (pshs_go k)
    | PCompact k => PCompact (match kc with Some g => g k | None => pshs_go k end)
    | PVia j js lo karms k => PVia j (sf js) (f lo) (pshs_go karms) (pshs_go k)
    | PMerge j => PMerge j
    | PAbstractCell b n k => PAbstractCell (esh b) n (pshs_go k)
    | PHavocWords bs k => PHavocWords (map esh bs) (pshs_go k)
    | PRespell r e k => PRespell r (esh e) (pshs_go k)
    | PMmapInH a b c => PMmapInH (pshs_go a) (pshs_go b) (pshs_go c)
    | PJoinX b off n k => PJoinX (esh b) off n (pshs_go k)
    | PDiamondT joinpc depth rs k => PDiamondT joinpc depth rs (pshs_go k)
    | PBand v klow khigh => PBand (f v) (pshs_go klow) (pshs_go khigh)
    | PIntroG lo hi n k => PIntroG lo hi n (pshs_go k)
    | PDiamondDisj b1 b2 joinpc rs k => PDiamondDisj (esh b1) (esh b2) joinpc rs (pshs_go k)
    | PDiamondTX joinpc depth rs R k => PDiamondTX joinpc depth rs R (pshs_go k)
    | PGcDisj live k => PGcDisj (map esh live) (pshs_go k)
    | PGcRangeAuto k => PGcRangeAuto (pshs_go k)
    end.
  Definition pshs : plan -> plan := pshs_go.
  End Plans.
  Definition psh : plan -> plan := pshs ash None true.
End Shift.

(* an increasing map read from a run: [vshift_tab t v] adds to [v] every delta whose threshold is at
   most [v] (old numbering); [t] lists (threshold, delta) pairs *)
Fixpoint vshift_tab (t : list (nat * nat)) (v : nat) : nat :=
  match t with
  | [] => v
  | (th, d) :: rest => if Nat.ltb v th then vshift_tab rest v else (vshift_tab rest v + d)%nat
  end.
Definition vshift (th d : nat) (v : nat) : nat := if Nat.ltb v th then v else (v + d)%nat.

(* ---- hand-off tables, joins, collection ---- *)
Fixpoint hlookup (m : list (nat * acs)) (h : nat) : option acs :=
  match m with
  | [] => None
  | (k, a) :: r => if Nat.eqb k h then Some a else hlookup r h
  end.
Fixpoint hupd (h : nat) (a : acs) (m : list (nat * acs)) : list (nat * acs) :=
  match m with
  | [] => [(h, a)]
  | (k, b) :: r => if Nat.eqb k h then (h, a) :: r else (k, b) :: hupd h a r
  end.

(* the first state, keeping only the facts the second also lists (as [entails] accepts them), the
   larger counter, and the looser of each size bound *)
Definition join_states (a b : acs) : acs :=
  let kb := kn b in
  let ka := List.filter (fun K => existsb (kentry_eqb K) kb || kimg_sub_covered0 kb K) (kn a) in
  let ss := a_ss a in
  ACS (SSR (s_pc ss) (s_regs ss) (s_log ss) ka (Nat.max (nxt a) (nxt b)) (s_resv ss))
      (a_maps a) (Z.max (a_totsz a) (a_totsz b)) (Z.min (a_ylo a) (a_ylo b))
      (Z.max (a_eager a) (a_eager b)) (a_vis a) (a_ghost a) (Z.max (a_abytes a) (a_abytes b))
      (a_brk a) (a_fd a) (a_tidset a).

(* [run js] is the certificate's own check with hand-off table [js] *)
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

(* several runs against one table (the two CONFIG_RSEQ values): the table one run leaves is where
   the next starts, until none moves it *)
Fixpoint collect_runs (fuel : nat) (runs : list ((nat -> option acs) -> cres)) (m : list (nat * acs)) : list (nat * acs) :=
  match fuel with
  | O => m
  | S f => collect_runs f runs (fold_left (fun m0 run => collect_handoffs 20 run m0) runs m)
  end.

(* ---- the facts a computed hand-off state keeps, and the later recorded states ----
   (double-conversion/string_to_double_fuzzer's PlanRegen.v, over this unit's state type.)
   A state the run reaches holds every fact the run derived; the recorded states the later plans
   were written against kept fewer.  [keep_facts]: every fact of the run on launch variables only
   (below NX0), and a fact naming a fresh variable only when the recorded state, renumbered, has
   it; laid out in the recorded state's order, a recorded fact the run lacks replaced in place by
   the run's fact about the same place ([counterpart]) or by [KTRUE], a fact every state
   satisfies.  Every kept fact is the run's own, and the certificate that names the state
   re-checks it. *)
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
  let ss := a_ss a in
  ACS (SSR (s_pc ss) (s_regs ss) (s_log ss) (k1 ++ k2) (s_next ss) (s_resv ss))
      (a_maps a) (a_totsz a) (a_ylo a) (a_eager a) (a_vis a) (a_ghost a) (a_abytes a) (a_brk a) (a_fd a) (a_tidset a).

(* The later recorded states in the new launch layout: each is renumbered and carries facts on
   launch variables that the old layout gave and the new one does not ([D], read off the recorded
   hand-off state against the computed one), and lacks the new layout's ([L], the other way
   round).  [relaunch nx0 D L] replaces each [D] fact in place by its [counterpart] in [L] (or
   [KTRUE]) and puts last the [L] facts that name a launch variable and are no [D] fact's
   counterpart.  An [L] fact that names no variable (a word at a fixed address of the image, a
   [KImg] piece) is not put last: it is a fact about the image's memory at the start-up hand-off,
   which the later code writes, so a later recorded state cannot carry it.  A register holding the
   value a [D] word fact gives holds its counterpart's value instead ([vmap]); a constant value is
   not mapped (a register holding 0 is no launch value: the start-up probe found the run's
   registers equal to the renumbered recorded ones).  A word fact on launch variables only (below
   [nx0]) that is no [D] fact holds the mapped value too ([kval]): the old run derived it from a
   [D] fact (the word at the entry stack pointer + 16 holds argv[1], which the start-up hand-off
   gives as [SLTU 1 argc * argv1] and later states as the pointer alone), and the new run holds
   its counterpart's.  Every state is checked again by the certificate that uses it. *)
Definition vmap (D L : list kentry) : list (expr * expr) :=
  flat_map (fun K => match K, counterpart L K with
                     | KWord _ _ (ELit _), _ => []
                     | KWord _ _ v, KWord _ _ v' =>
                         (v, v') :: match v, v' with EMd _ _ x, EMd _ _ x' => [(x, x')] | _, _ => [] end
                     | _, _ => []
                     end) D.
Definition erepl1 (m : list (expr * expr)) (e : expr) : expr :=
  match find (fun q => expr_eqb (fst q) e) m with Some q => snd q | None => e end.
Definition kval (nx0 : nat) (m : list (expr * expr)) (K : kentry) : kentry :=
  match K with
  | KWord a w v => if launch_only nx0 K then KWord a w (erepl1 m v) else K
  | _ => K
  end.
Definition var_free (K : kentry) : bool := match kvars_of K with [] => true | _ => false end.
Definition relaunch (nx0 : nat) (D L : list kentry) (S : acs) : acs :=
  let ss := a_ss S in
  let m := vmap D L in
  let S1 := ACS (SSR (s_pc ss) (map (erepl1 m) (s_regs ss)) (s_log ss) (s_know ss) (s_next ss) (s_resv ss))
                (a_maps S) (a_totsz S) (a_ylo S) (a_eager S) (a_vis S) (a_ghost S) (a_abytes S) (a_brk S) (a_fd S) (a_tidset S) in
  let k1 := map (fun K => if kin K D then counterpart L K else kval nx0 m K) (kn S) in
  set_kn S1 (k1 ++ filter (fun K => andb (negb (var_free K)) (andb (negb (kin K k1)) (negb (existsb (fun Kd => same_key Kd K) D)))) L).

(* the four size bounds a later state carries move by what the launch moved them: the computed
   hand-off state's value less the recorded one's *)
Definition resize (dt dy de da : Z) (S : acs) : acs :=
  ACS (a_ss S) (a_maps S) (a_totsz S + dt)%Z (a_ylo S + dy)%Z (a_eager S + de)%Z (a_vis S) (a_ghost S)
      (a_abytes S + da)%Z (a_brk S) (a_fd S) (a_tidset S).

(* A recorded [PForget] that the new run applies to another fact than the old run did
   (double-conversion/string_to_double_fuzzer's PlanRegen.v, over this unit's plan type).  The
   forget lists are indices into the knowledge the old run held there; where the new run's
   knowledge before such a node differs from the old one's, the same index names another fact.
   Fixed rule, applied in the build along each path of a plan to a given hand-off: at each
   [PForget] on that path, an index that names a fact with no variable which the hand-off state
   carries is left out of the list ([forget_keep]).  A [PForget] only weakens a state, so any index
   list checks as soundly; the certificate re-runs the check on the plan this gives. *)
Definition kids (p : plan) : list plan :=
  match p with
  | PRun _ k | PShDisj _ _ _ _ k | PFact _ k | PJoin _ _ _ k | PForget _ k | PDropRange _ _ k | PGcKeep _ k
  | PBump _ k | PHavoc _ k | PHavocBig _ k | PFresh _ _ _ k | PSys _ k | PX _ _ k | PExt _ _ k | PEmit _ _ k
  | PFog _ _ k | PFogNew _ _ k | PGhost _ _ k | PUnvis _ _ k | PHavocBrk _ _ k | PIntro _ _ k | PDiamond _ _ k
  | PRename _ k | PCompact k | PAbstractCell _ _ k | PHavocWords _ k | PRespell _ _ k | PJoinX _ _ _ k
  | PDiamondT _ _ _ k | PIntroG _ _ _ k | PDiamondDisj _ _ _ _ k | PDiamondTX _ _ _ _ k | PGcDisj _ k
  | PGcRangeAuto k => [k]
  | PSplit _ _ a b | PCase2 _ _ a b | PCaseDisj _ _ a b | PMmap a b | PMprotect a b | PBrk2 a b
  | PExt2 _ _ a b | PLoop _ _ _ a b | PVia _ _ _ a b | PBand _ a b => [a; b]
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
  | PFresh a b c _ => PFresh a b c q | PSys y _ => PSys y q | PX x a _ => PX x a q
  | PExt i0 a _ => PExt i0 a q | PEmit i0 a _ => PEmit i0 a q | PFog a b _ => PFog a b q | PFogNew a b _ => PFogNew a b q
  | PGhost a b _ => PGhost a b q | PUnvis a b _ => PUnvis a b q | PHavocBrk a b _ => PHavocBrk a b q
  | PIntro a b _ => PIntro a b q | PDiamond a b _ => PDiamond a b q | PRename m _ => PRename m q
  | PCompact _ => PCompact q | PAbstractCell a b _ => PAbstractCell a b q | PHavocWords a _ => PHavocWords a q
  | PRespell a b _ => PRespell a b q | PJoinX a b c _ => PJoinX a b c q | PDiamondT a b c _ => PDiamondT a b c q
  | PIntroG a b c _ => PIntroG a b c q | PDiamondDisj a b c d _ => PDiamondDisj a b c d q
  | PDiamondTX a b c d _ => PDiamondTX a b c d q | PGcDisj l _ => PGcDisj l q | PGcRangeAuto _ => PGcRangeAuto q
  | PSplit e m a b => PSplit e m (pick 0%nat a) (pick 1%nat b)
  | PCase2 e m a b => PCase2 e m (pick 0%nat a) (pick 1%nat b)
  | PCaseDisj x y a b => PCaseDisj x y (pick 0%nat a) (pick 1%nat b)
  | PMmap a b => PMmap (pick 0%nat a) (pick 1%nat b)
  | PMprotect a b => PMprotect (pick 0%nat a) (pick 1%nat b)
  | PBrk2 a b => PBrk2 (pick 0%nat a) (pick 1%nat b)
  | PExt2 i0 x a b => PExt2 i0 x (pick 0%nat a) (pick 1%nat b)
  | PLoop J N inv a b => PLoop J N inv (pick 0%nat a) (pick 1%nat b)
  | PVia j js lo a b => PVia j js lo (pick 0%nat a) (pick 1%nat b)
  | PBand v a b => PBand v (pick 0%nat a) (pick 1%nat b)
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

(* ---- hand-off states and FX end states computed in the build ----
   [hcoll nx0 ls tmpl h]: the state a check hands off at [h], from its leaves [ls] (one pass of
   [CAP.collect], the check's own run): the join of every leaf at [h], its facts chosen by
   [keep_facts] against the recorded state [tmpl] renumbered (no leaf at [h]: [tmpl]).  The
   certificate that produces it re-checks it as its hand-off, and each consumer starts from it. *)
Definition hjoin (ls : list (nat * acs)) (h : nat) : option acs :=
  match List.filter (fun p => Nat.eqb (fst p) h) ls with
  | (_, a) :: r => Some (fold_left (fun acc q => join_states acc (snd q)) r a)
  | [] => None
  end.
Definition hcoll (nx0 : nat) (ls : list (nat * acs)) (tmpl : acs) (h : nat) : acs :=
  match hjoin ls h with Some a => keep_facts nx0 tmpl a | None => tmpl end.

(* [fx_end rx S0 S0r Er]: the end state of an FX hole from start [S0], recorded as [Er] after the
   recorded start [S0r], with its total-size bound computed from [S0].  The FX ledger starts from
   [a_totsz S0 - R0], which counts the launch's extra reserved pair (at most [rx] bytes,
   [CXS.co_resx]) as mapped space, and the leaf's bound adds [rx] again ([Br3Leaf.same3_chk]); so
   the end bound is the start's plus [rx] plus the hole's recorded growth.  The hole re-checks the
   state ([trans3h_chk]). *)
Definition set_totsz (S : acs) (t : Z) : acs :=
  ACS (a_ss S) (a_maps S) t (a_ylo S) (a_eager S) (a_vis S) (a_ghost S) (a_abytes S) (a_brk S) (a_fd S) (a_tidset S).
Definition fx_end (rx : Z) (S0 S0r Er : acs) : acs :=
  set_totsz Er (a_totsz S0 + rx + (a_totsz Er - a_totsz S0r))%Z.
