(* SPDX-License-Identifier: MIT *)
(* A plan's variable renumbering, [psh f], applied where the plan is checked, so a
   recorded plan is not rewritten by hand.  After jsoncons/fuzz_bigint's PlanRegenK.v
   ([esh], [ksh], [psh]), over this unit's [AP.plan] and [AX2.kentry].

   WHY: at LPS 727298f3 the launch gives one more plan variable ([V_GID], NXS 14 -> 15)
   and musl's auxv walk reads more of the vector, so the start-up run allocates its
   fresh variables at other numbers than the run the recorded plans were written
   against.  A plan that names a fresh variable then names the wrong one.  Each map
   is read off the new run (the counters the run reaches at its hand-offs, printed by
   a probe), never chosen.

   WHICH plan fields are variables, read from [AP.checkA]'s arms: [PBump m] (the
   counter), [PLoop J] / [PLoopM J], [PVia lo] / [PViaM lo], both sides of
   [PRename], the placeholder [ph] of [PFactLeX] / [PFactX] (substituted in [e]), the
   variable side of each [(nat * expr)] widening list, and every embedded [expr] and
   [kentry].  Every other nat field stays: registers ([PHavoc], [PFresh],
   [PDiamond], [PRespell], [PCaseReg], [PFactLeR], [PFactR], the [r] of [PFactLeX] /
   [PFactX]), list indices ([PForget], [PFog], [PFogNew]), ids ([PExt], [PEmit],
   [PExt2], [PAlt2], [PTerm], [PHandoff], [PHandoffW], [PMerge], [PMergeW],
   [PContraH], [PVia j]) and counts ([PJoin], [PHavocBig]).  The states written
   inside [PLoop], [PLoopM], [PVia] and [PViaM] are not renumbered.
   Soundness does not rest on this classification: every certificate computes through
   [psh] and re-checks the renumbered plan, so a wrong map or classification can only
   make a certificate fail. *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AzSymExec3 AzSymExec3B AzPlanCore AzPlan.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.

Section Shift.
  Variable f : nat -> nat.
  (* what each hand-off becomes: [PHandoff] for a plain renumbering *)
  Variable hnd : nat -> plan.

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
    | KShOk a n => KShOk (sash a) (esh n)
    | KFpc v lo d => KFpc (esh v) (esh lo) d
    end.
  Definition pesh (p : expr * expr) : expr * expr := (esh (fst p), esh (snd p)).
  Definition wsh (w : list (nat * expr)) : list (nat * expr) :=
    map (fun q => (f (fst q), esh (snd q))) w.

  Fixpoint pmap (p : plan) : plan :=
    match p with
    | PRun stops k => PRun stops (pmap k)
    | PSplit e mid k1 k2 => PSplit (esh e) mid (pmap k1) (pmap k2)
    | PCase2 e mid k1 k2 => PCase2 (esh e) mid (pmap k1) (pmap k2)
    | PCaseDisj b1 b2 k1 k2 => PCaseDisj (esh b1) (esh b2) (pmap k1) (pmap k2)
    | PShDisj b1 n1 b2 n2 k => PShDisj (esh b1) (esh n1) (esh b2) (esh n2) (pmap k)
    | PContra => PContra
    | PFact K k => PFact (ksh K) (pmap k)
    | PJoin b off n k => PJoin (esh b) off n (pmap k)
    | PForget ixs k => PForget ixs (pmap k)
    | PDropRange b n k => PDropRange (esh b) (esh n) (pmap k)
    | PGcKeep ws k => PGcKeep (map pesh ws) (pmap k)
    | PBump m k => PBump (f m) (pmap k)
    | PHavoc rs k => PHavoc rs (pmap k)
    | PHavocBig K k => PHavocBig K (pmap k)
    | PFresh r logc base k => PFresh r logc (option_map esh base) (pmap k)
    | PSys y k => PSys y (pmap k)
    | PMmap ka kb => PMmap (pmap ka) (pmap kb)
    | PMmapIn a b c => PMmapIn (pmap a) (pmap b) (pmap c)
    | PMprotect a b => PMprotect (pmap a) (pmap b)
    | PBrk2 a b => PBrk2 (pmap a) (pmap b)
    | PX x args k => PX x (map esh args) (pmap k)
    | PExt id args k => PExt id (map esh args) (pmap k)
    | PEmit id args k => PEmit id (map esh args) (pmap k)
    | PExt2 id args k1 k2 => PExt2 id (map esh args) (pmap k1) (pmap k2)
    | PLoop J N inv w body k => PLoop (f J) (esh N) inv (wsh w) (pmap body) (pmap k)
    | PNext => PNext
    | PHandoff h => hnd h
    | PExit => PExit
    | PSpin => PSpin
    | PFog i sz k => PFog i sz (pmap k)
    | PFogNew i sz k => PFogNew i sz (pmap k)
    | PGhost b n k => PGhost (esh b) (esh n) (pmap k)
    | PUnvis b n k => PUnvis (esh b) (esh n) (pmap k)
    | PHavocBrk lo hi k => PHavocBrk lo hi (pmap k)
    | PIntro lo hi k => PIntro lo hi (pmap k)
    | PDiamond joinpc rs k => PDiamond joinpc rs (pmap k)
    | PRename m k => PRename (map (fun q => (f (fst q), f (snd q))) m) (pmap k)
    | PCompact k => PCompact (pmap k)
    | PVia j js lo karms k => PVia j js (f lo) (pmap karms) (pmap k)
    | PMerge j => PMerge j
    | PAbstractCell b n k => PAbstractCell (esh b) n (pmap k)
    | PHavocWords bs k => PHavocWords (map esh bs) (pmap k)
    | PRespell r e k => PRespell r (esh e) (pmap k)
    | PMmapInH a b c => PMmapInH (pmap a) (pmap b) (pmap c)
    | PNextW w => PNextW (wsh w)
    | PMergeW j w => PMergeW j (wsh w)
    | PBranch a b => PBranch (pmap a) (pmap b)
    | PCaseReg r mid k1 k2 => PCaseReg r mid (pmap k1) (pmap k2)
    | PFactVia e via lo hi k => PFactVia (esh e) (esh via) lo hi (pmap k)
    | PHandoffW h w => PHandoffW h (wsh w)
    | PFactLe e big hi k => PFactLe (esh e) (esh big) hi (pmap k)
    | PFactScale e c hi k => PFactScale (esh e) c hi (pmap k)
    | PFactLeR r off big hi k => PFactLeR r off (esh big) hi (pmap k)
    | PFactR r off lo hi k => PFactR r off lo hi (pmap k)
    | PFactLeX r ph e big hi k => PFactLeX r (f ph) (esh e) (esh big) hi (pmap k)
    | PFactX r ph e lo hi k => PFactX r (f ph) (esh e) lo hi (pmap k)
    | PContraH h => PContraH h
    | PLoopM J N alts w =>
        PLoopM (f J) (esh N)
          (map (fun a => match a with (inv, body, k) => (inv, pmap body, pmap k) end) alts) (wsh w)
    | PViaM j alts lo karms => PViaM j (map (fun a => (fst a, pmap (snd a))) alts) (f lo) (pmap karms)
    | PBranchP a b => PBranchP (pmap a) (pmap b)
    | PAlt2 id args ka kb => PAlt2 id (map esh args) (pmap ka) (pmap kb)
    | PUnreach => PUnreach
    | PMmapW lo hi a b c => PMmapW lo hi (pmap a) (pmap b) (pmap c)
    | PMmapH a b => PMmapH (pmap a) (pmap b)
    | PTerm id args => PTerm id (map esh args)
    end.
End Shift.

(* The renumbering of a plan; [pmap f g] also ends each hand-off [h] with [g h] (for a
   rename and a counter bump before a hand-off). *)
Definition psh (f : nat -> nat) (p : plan) : plan := pmap f PHandoff p.

(* The pairs (v, g v) for v in [lo, hi): a renaming by a map read off the runs, for
   [PRename]. *)
Definition rename_pairs (g : nat -> nat) (lo hi : nat) : list (nat * nat) :=
  map (fun v => (v, g v)) (seq lo (hi - lo)).

(* The maps read off the runs: variables below [lo] keep their numbers, the others
   move up by [d]. *)
Definition vsh_from (lo d v : nat) : nat := if Nat.ltb v lo then v else v + d.
(* A map in two steps: below [lo] kept, [lo] .. [b2 - 1] up by [d1], from [b2] up by
   [d2] (a plan whose run allocates more variables from some node on). *)
Definition vsh_two (lo d1 b2 d2 v : nat) : nat :=
  if Nat.ltb v lo then v else if Nat.ltb v b2 then v + d1 else v + d2.

(* The states a run hands off, computed from the run (after jsoncons/fuzz_bigint's
   PlanRegenK.v [collect_handoffs] / [join_states]).  [AP.checkA]'s [PHandoff h] arm
   answers [CErr 4 (PHandoff h) cs] when the table has no state for [h], and
   [CErr 3 (PHandoff h) cs] when the reached [cs] does not entail the stored one; [cs] is
   then the state the run reaches there.  [collect_handoffs] reruns the check: a missing
   state becomes the reached one, and a stored state another path does not entail
   becomes the join of the two.  A state computed this way is a definition, not an
   assumption: the certificate that names it reruns the check, which must entail it.
   [canon] names the hand-offs that share one state (a plan that hands off to several
   ids through one table entry). *)
(* The facts both states have, and for a [KRange] on one expression in both, the
   range that covers both (the two paths bound one variable differently); the
   budgets the hand-off check compares one way ([a_totsz], [a_eager], [a_abytes] at
   most the stored one, [a_ylo] at least) taken at the bound that covers both;
   every other part from [a]. *)
Fixpoint krange_of (k : list kentry) (e : expr) : option (Z * Z) :=
  match k with
  | [] => None
  | K :: r => match K with
              | KRange e' lo hi => if expr_eqb e e' then Some (lo, hi) else krange_of r e
              | _ => krange_of r e
              end
  end.
Definition join_states (a b : acs) : acs :=
  let kn' := List.flat_map (fun K =>
               if existsb (kentry_eqb K) (kn b) then [K] else
               match K with
               | KRange e lo hi => match krange_of (kn b) e with
                                   | Some (lo', hi') => [KRange e (Z.min lo lo') (Z.max hi hi')]
                                   | None => []
                                   end
               | _ => []
               end) (kn a) in
  let a1 := set_kn a kn' in
  let ss := a_ss a1 in
  ACS (mk_ss (s_pc ss) (s_regs ss) (s_know ss) (Nat.max (nxt a) (nxt b)))
      (a_maps a) (Z.max (a_totsz a) (a_totsz b)) (Z.min (a_ylo a) (a_ylo b))
      (Z.max (a_eager a) (a_eager b)) (a_vis a) (a_ghost a) (Z.max (a_abytes a) (a_abytes b))
      (a_brk a) (a_fd a) (a_tidset a) (a_meter a) (a_fake a) (a_fbud a).

Section Collect.
  Variable canon : nat -> nat.

  Definition hlookup (m : list (nat * acs)) (h : nat) : option acs :=
    match List.find (fun q => Nat.eqb (fst q) (canon h)) m with Some q => Some (snd q) | None => None end.
  Definition hupd (h : nat) (a : acs) (m : list (nat * acs)) : list (nat * acs) :=
    (canon h, a) :: List.filter (fun q => negb (Nat.eqb (fst q) (canon h))) m.

  (* [run t] is the certificate's own check with hand-off table [t]. *)
  Fixpoint collect_handoffs (fuel : nat) (run : (nat -> option acs) -> cres)
      (m : list (nat * acs)) : list (nat * acs) :=
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

  (* the state at hand-off [h], or [dflt] when the run never reaches it *)
  Definition hstate (m : list (nat * acs)) (dflt : acs) (h : nat) : acs :=
    match hlookup m h with Some a => a | None => dflt end.

  (* The plans of a lane in an order where each plan's start hand-off is collected
     before it runs: (start hand-off, payload).  [run x st t] is the certificate's
     check of the payload's plan from state [st] with table [t] (the payload carries
     the plan and whatever else its check takes, such as its instruction table). *)
  Fixpoint collect_pass {X : Type} (fuel : nat) (run : X -> acs -> (nat -> option acs) -> cres)
      (es : list (nat * X)) (m : list (nat * acs)) : list (nat * acs) :=
    match es with
    | [] => m
    | (src, x) :: rest =>
        match hlookup m src with
        | Some st => collect_pass fuel run rest (collect_handoffs fuel (run x st) m)
        | None => collect_pass fuel run rest m
        end
    end.
End Collect.
