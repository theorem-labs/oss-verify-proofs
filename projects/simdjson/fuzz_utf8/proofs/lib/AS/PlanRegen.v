(* SPDX-License-Identifier: MIT *)
(* Recorded start-up data made again for LPS 727298f3, over this unit's plan and state types
   (AsanPlan.plan, AsanPlanCore.acs).  The text of simdjson/fuzz_parser's AS/PlanRegen.v (this
   unit's twin plan checker, the same plan and state types); that file was made from
   spirv-tools/spvtools_binary_parser_fuzzer's bpA/Start/AsPlanRegen.v (the renumbering) and
   jsoncons/fuzz_bigint's PlanRegenK.v (collect_handoffs, join_states; the bounds of join_states
   as skcms's PlanRegen.v takes them).

   1. [psh f p]: a recorded plan's variable renumbering, a total increasing map [f] applied where
      the plan is checked, so the recorded plan is never rewritten.  The launch has more plan
      variables at 727298f3 ([V_G], [V_GID]) and the run reads more of the auxv, so the run
      allocates its fresh variables at other numbers than the run the plans were written against.
      The map is read off a probe of the new run, never chosen.
      Which plan fields are variables, read from [AsanPlan.check]'s arms: PBump m, PLoop J,
      PRename (both sides), PVia lo, and every embedded expr, kentry and state.  Every other nat
      field stays (registers, widths, list indices, ids, counts, size thresholds).
      SOUNDNESS DOES NOT REST ON THIS CLASSIFICATION: a certificate re-checks the renumbered plan,
      so a wrong map or classification can only make a certificate fail.
   2. [collect_handoffs]: the hand-off states, computed in the build by re-running the
      certificate's own check with the table found so far.  A state computed this way is a
      definition: the certificate that names it checks the plan again and the state the run
      reaches there must imply it. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

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

(** A step map: [vsteps [(b1, d1); ...] v] moves [v] up by the sum of the [di] with [bi <= v].
    With every [di] nonnegative it is increasing and defined for every number; the variables
    below the least [bi] (the launch's own) keep their numbers. *)
Fixpoint vsteps (l : list (nat * nat)) (v : nat) : nat :=
  match l with
  | [] => v
  | (b, d) :: r => (if Nat.leb b v then d else 0) + vsteps r v
  end%nat.

(** A recorded split's constant on one expression, moved: [pmid e0 d p] adds [d] to the constant of
    every [PSplit e0 mid _ _] of [p] and leaves every other node as it is.  At 727298f3 the auxv
    is [AUXSZ rz] bytes where the plans were recorded against 160, so [e_atr8] (AT_RANDOM / 8,
    less the three words below the auxv and the auxv itself: [e_atrandom], [e_atr8] in
    AsanPlanCore, against the old [e_atrandom := e_auxv + 160 + 8 V_W]) is [(AUXSZ rz - 160) / 8]
    smaller at the same AT_RANDOM address.  A split on [e_atr8] names AT_RANDOM positions (the
    shadow words of its sixteen bytes), so its constant moves by [atr8_shift rz].  The
    certificate re-checks the moved plan, so a wrong shift can only make it fail. *)
Definition atr8_shift (rz : Z) : Z := (160 - AUXSZ rz) / 8.
Section Mid.
  Variable e0 : expr.
  Variable d : Z.
  Fixpoint pmid (p : plan) : plan :=
    match p with
    | PRun stops k => PRun stops (pmid k)
    | PSplit e mid k1 k2 => PSplit e (if expr_eqb e e0 then mid + d else mid) (pmid k1) (pmid k2)
    | PCase2 e mid k1 k2 => PCase2 e mid (pmid k1) (pmid k2)
    | PCaseDisj b1 b2 k1 k2 => PCaseDisj b1 b2 (pmid k1) (pmid k2)
    | PShDisj b1 n1 b2 n2 k => PShDisj b1 n1 b2 n2 (pmid k)
    | PContra => PContra
    | PFact K k => PFact K (pmid k)
    | PJoin b off n k => PJoin b off n (pmid k)
    | PForget ixs k => PForget ixs (pmid k)
    | PDropRange b n k => PDropRange b n (pmid k)
    | PGcKeep ws k => PGcKeep ws (pmid k)
    | PBump m k => PBump m (pmid k)
    | PHavoc rs k => PHavoc rs (pmid k)
    | PHavocBig K k => PHavocBig K (pmid k)
    | PFresh r logc base k => PFresh r logc base (pmid k)
    | PSys y k => PSys y (pmid k)
    | PMmap ka kb => PMmap (pmid ka) (pmid kb)
    | PMmapIn ka kb kc => PMmapIn (pmid ka) (pmid kb) (pmid kc)
    | PMprotect ka kb => PMprotect (pmid ka) (pmid kb)
    | PBrk2 ka kb => PBrk2 (pmid ka) (pmid kb)
    | PX x args k => PX x args (pmid k)
    | PExt id args k => PExt id args (pmid k)
    | PEmit id args k => PEmit id args (pmid k)
    | PExt2 id args k1 k2 => PExt2 id args (pmid k1) (pmid k2)
    | PLoop J N inv body k => PLoop J N inv (pmid body) (pmid k)
    | PNext => PNext
    | PHandoff h => PHandoff h
    | PExit => PExit
    | PSpin => PSpin
    | PFog i sz k => PFog i sz (pmid k)
    | PFogNew i sz k => PFogNew i sz (pmid k)
    | PGhost b n k => PGhost b n (pmid k)
    | PUnvis b n k => PUnvis b n (pmid k)
    | PHavocBrk lo hi k => PHavocBrk lo hi (pmid k)
    | PIntro lo hi k => PIntro lo hi (pmid k)
    | PDiamond joinpc rs k => PDiamond joinpc rs (pmid k)
    | PRename m k => PRename m (pmid k)
    | PCompact k => PCompact (pmid k)
    | PVia j js lo karms k => PVia j js lo (pmid karms) (pmid k)
    | PMerge j => PMerge j
    | PAbstractCell b n k => PAbstractCell b n (pmid k)
    | PHavocWords bs k => PHavocWords bs (pmid k)
    | PRespell r e k => PRespell r e (pmid k)
    | PMmapInH ka kb kc => PMmapInH (pmid ka) (pmid kb) (pmid kc)
    end.
End Mid.

(** The hand-off table found so far, as a list, and its lookup. *)
Fixpoint hlookup (m : list (nat * acs)) (h : nat) : option acs :=
  match m with
  | [] => None
  | (h', a) :: r => if Nat.eqb h h' then Some a else hlookup r h
  end.
Definition hupd (h : nat) (a : acs) (m : list (nat * acs)) : list (nat * acs) :=
  (h, a) :: List.filter (fun p => negb (Nat.eqb (fst p) h)) m.

(** The form a reached state is stored in as a hand-off state: the store log and the
    reservation dropped.  [entails] reads neither of the stored state, so this changes no
    answer of a hand-off test. *)
Definition hform (cs : acs) : acs :=
  let ss := a_ss cs in with_ss cs (SSR (s_pc ss) (s_regs ss) [] (s_know ss) (s_next ss) None).

(** Two reached states at one hand-off: the first one, keeping only the facts both list, the
    larger counter, and the looser of each size bound ([entails] wants the reached state's
    [a_totsz], [a_eager], [a_abytes] at most the stored ones and its [a_ylo] at least).  It helps
    only where the two differ in those; [entails] needs the rest equal. *)
Definition join_states (a b : acs) : acs :=
  let ss := a_ss a in
  ACS (SSR (s_pc ss) (s_regs ss) [] (List.filter (fun K => existsb (kentry_eqb K) (kn b)) (kn a))
           (Nat.max (s_next ss) (nxt b)) None)
      (a_maps a) (Z.max (a_totsz a) (a_totsz b)) (Z.min (a_ylo a) (a_ylo b)) (Z.max (a_eager a) (a_eager b))
      (a_vis a) (a_ghost a) (Z.max (a_abytes a) (a_abytes b)) (a_brk a) (a_fd a) (a_tidset a).

(** [run js] is the certificate's own check with hand-off table [js].  At a hand-off the table
    lacks ([CErr 4]) the reached state becomes its entry; at one whose entry the reached state
    does not imply ([CErr 3]) the entry becomes the join of the two.  Any other answer stops the
    collection with the table as it is, so a node refused elsewhere shows in the build as a
    failing certificate. *)
Fixpoint collect_handoffs (fuel : nat) (run : (nat -> option acs) -> cres) (m : list (nat * acs))
  : list (nat * acs) :=
  match fuel with
  | O => m
  | S f =>
      match run (hlookup m) with
      | CErr code (PHandoff h) cs =>
          if Z.eqb code 4 then collect_handoffs f run (hupd h (hform cs) m)
          else if Z.eqb code 3 then
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
