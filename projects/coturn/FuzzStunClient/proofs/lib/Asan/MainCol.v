(* SPDX-License-Identifier: MIT *)
(* coturn MAIN TEMPLATE COLLECTOR. A computation, not a proof: it proves nothing and no certificate
   depends on it. It produces the per-r template states the main certificates are then re-checked against.

   It works on a main tree node ([MPre] / [MPreS] / [MPreX]) with ANY number of holes and joins:
     run the node's check with the current hole table H (as the check's HS) and the current join table J
     (substituted into the plan's [PVia] nodes by [pjs]);
     COk           -> done, with the node's shape;
     a refusal (code 3) or a missing entry (code 4) at [PHandoff h] -> H(h) := the arriving state (the first time
                      in this run, so a stale seed is discarded) or its meet with H(h) (every later time);
     the same at [PMerge j]                                       -> J(j) := likewise;
     anything else -> stop, with the refusing row (code, pc, tag, nxt) logged.
   A loop invariant ([PLoop inv] / [PNext]) refusal is in "anything else": it stops the run and is logged.

   Rows: one per round, (code, pc, tag, nxt), tag = 100 + h for a hole, 1000 + j for a join, 0 otherwise; the
   final row of a converged run is (0, 0, 0, 0). The iteration count of a run is the length of its log. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* The arriving state with its log and reservation dropped: what a hand-off / join entry may hold. *)
Definition mc_clean (c : acs) : acs :=
  let s := a_ss c in
  {| a_ss := SSR (s_pc s) (s_regs s) [] (s_know s) (s_next s) None; a_maps := a_maps c; a_totsz := a_totsz c;
     a_ylo := a_ylo c; a_eager := a_eager c; a_vis := a_vis c; a_ghost := a_ghost c; a_abytes := a_abytes c;
     a_brk := a_brk c; a_fd := a_fd c; a_tidset := a_tidset c |}.
(* [mc_keepK c K]: the test the HAND-OFF itself applies to one recorded fact, read off
   [AsanPlanCore.entails_ref]'s knowledge conjunct, which [entails_eq] proves equal to the
   [entails] that [PHandoff h] runs:
     forallb (fun K => existsb (kentry_eqb K) (kn cs) || existsb (fun X => kpriv_geb X K) (kn cs)) (kn ch)
   A collected table may hold K exactly when this holds of the arriving state, no more and no
   less: both disjuncts are needed, since a KPriv the hand-off accepts must stay in the table. *)
Definition mc_keepK (c : acs) (K : kentry) : bool :=
  (existsb (kentry_eqb K) (kn c) || existsb (fun X => kpriv_geb X K) (kn c))%bool.

(* The facts of [c0] that [c] still entails, and the weaker of each bound: every state entailing either entails
   this on the knowledge and bound fields. Registers, maps, vis, ghost, brk, fd stay [c0]'s; [entails] needs them
   syntactically equal, so an arrival differing there is refused again and the run stops on fuel. *)
Definition mc_meet (c0 c : acs) : acs :=
  let s := a_ss c0 in
  {| a_ss := SSR (s_pc s) (s_regs s) [] (List.filter (mc_keepK c) (s_know s)) (s_next s) None;
     a_maps := a_maps c0; a_totsz := Z.max (a_totsz c0) (a_totsz c); a_ylo := Z.min (a_ylo c0) (a_ylo c);
     a_eager := Z.max (a_eager c0) (a_eager c); a_vis := a_vis c0; a_ghost := a_ghost c0;
     a_abytes := Z.max (a_abytes c0) (a_abytes c); a_brk := a_brk c0; a_fd := a_fd c0; a_tidset := a_tidset c0 |}.

(* FIRST-REFUSAL REPLACEMENT.  [mc_clean] records the arriving state's [s_know] VERBATIM, so a fact
   the seed holds and the arrival only ENTAILS would vanish from the table on the very first refusal of a run -- no
   meet is involved ([seen] is false, so the seed is discarded outright).
   [mc_clean_keep] adds back exactly those seed facts the ARRIVAL ITSELF ENTAILS, by the hand-off's own test.  It can
   add nothing the arrival does not imply, so [entails cs ch] still holds of the result; and every table this
   file emits is re-checked by a certificate, which is the second guard. *)
Definition mc_clean_keep (c0 c : acs) : acs :=
  let b := mc_clean c in
  set_kn b (kn b ++ List.filter (fun K => (negb (existsb (kentry_eqb K) (kn b)) && mc_keepK c K)%bool) (kn c0)).

Definition mc_tag (p : plan) : Z :=
  match p with PMerge j => 1000 + Z.of_nat j | PHandoff h => 100 + Z.of_nat h | _ => 0 end.

Fixpoint tlook (T : list (nat * acs)) (h : nat) : option acs :=
  match T with [] => None | (h', s) :: T' => if Nat.eqb h h' then Some s else tlook T' h end.
Fixpoint tupd (T : list (nat * acs)) (h : nat) (v : acs) : list (nat * acs) :=
  match T with [] => [(h, v)] | (h', s) :: T' => if Nat.eqb h h' then (h, v) :: T' else (h', s) :: tupd T' h v end.
Definition jlook (J : list (nat * acs)) (j : nat) (d : acs) : acs :=
  match tlook J j with Some s => s | None => d end.

(* The plan with each [PVia j js] reading its join state from [J] (unchanged where [J] has no entry j). *)
Fixpoint pjs (J : list (nat * acs)) (p : plan) : plan :=
  match p with
  | PRun stops k => PRun stops (pjs J k)
  | PSplit e mid k1 k2 => PSplit e mid (pjs J k1) (pjs J k2)
  | PCase2 e mid k1 k2 => PCase2 e mid (pjs J k1) (pjs J k2)
  | PCaseDisj b1 b2 k1 k2 => PCaseDisj b1 b2 (pjs J k1) (pjs J k2)
  | PShDisj b1 n1 b2 n2 k => PShDisj b1 n1 b2 n2 (pjs J k)
  | PContra => p
  | PFact K k => PFact K (pjs J k)
  | PJoin b off n k => PJoin b off n (pjs J k)
  | PForget ixs k => PForget ixs (pjs J k)
  | PDropRange b n k => PDropRange b n (pjs J k)
  | PGcKeep ws k => PGcKeep ws (pjs J k)
  | PBump m k => PBump m (pjs J k)
  | PHavoc rs k => PHavoc rs (pjs J k)
  | PHavocBig K k => PHavocBig K (pjs J k)
  | PFresh r logc base k => PFresh r logc base (pjs J k)
  | PSys y k => PSys y (pjs J k)
  | PMmap ka kb => PMmap (pjs J ka) (pjs J kb)
  | PMmapIn a b c => PMmapIn (pjs J a) (pjs J b) (pjs J c)
  | PMprotect a b => PMprotect (pjs J a) (pjs J b)
  | PBrk2 a b => PBrk2 (pjs J a) (pjs J b)
  | PMunmap2 a b => PMunmap2 (pjs J a) (pjs J b)
  | PX x args k => PX x args (pjs J k)
  | PExt id args k => PExt id args (pjs J k)
  | PEmit id args k => PEmit id args (pjs J k)
  | PExt2 id args k1 k2 => PExt2 id args (pjs J k1) (pjs J k2)
  | PLoop J0 N inv body k => PLoop J0 N inv (pjs J body) (pjs J k)
  | PNext => p
  | PHandoff h => p
  | PExit => p
  | PSpin => p
  | PFog i sz k => PFog i sz (pjs J k)
  | PFogNew i sz k => PFogNew i sz (pjs J k)
  | PGhost b n k => PGhost b n (pjs J k)
  | PUnvis b n k => PUnvis b n (pjs J k)
  | PHavocBrk lo hi k => PHavocBrk lo hi (pjs J k)
  | PIntro lo hi k => PIntro lo hi (pjs J k)
  | PDiamond joinpc rs k => PDiamond joinpc rs (pjs J k)
  | PRename m k => PRename m (pjs J k)
  | PCompact k => PCompact (pjs J k)
  | PVia j js lo karms k => PVia j (jlook J j js) lo (pjs J karms) (pjs J k)
  | PMerge j => p
  | PAbstractCell b n k => PAbstractCell b n (pjs J k)
  | PHavocWords bs k => PHavocWords bs (pjs J k)
  | PRespell r e k => PRespell r e (pjs J k)
  | PMmapInH a b c => PMmapInH (pjs J a) (pjs J b) (pjs J c)
  | PCaseDisjJ b1 b2 joinpc rs k => PCaseDisjJ b1 b2 joinpc rs (pjs J k)
  | PCaseP k1 k2 => PCaseP (pjs J k1) (pjs J k2)
  | PCaseNJ e cuts joinpc rs ws k => PCaseNJ e cuts joinpc rs ws (pjs J k)
  | PVisAbsorb b n k => PVisAbsorb b n (pjs J k)
  | PFreshCell b n k => PFreshCell b n (pjs J k)
  | PVisSplit b n d k => PVisSplit b n d (pjs J k)
  | PVisHead b m L k => PVisHead b m L (pjs J k)
  | PUnvisHead b m k => PUnvisHead b m (pjs J k)
  | PGhostDedup k => PGhostDedup (pjs J k)
  | PHavocBrkP lo hi k => PHavocBrkP lo hi (pjs J k)
  | PKeep ws vs k => PKeep ws vs (pjs J k)
  | PFactMem K k => PFactMem K (pjs J k)
  | PVisRespell b n b' n' k => PVisRespell b n b' n' (pjs J k)
  | PMapRespell b n b' n' k => PMapRespell b n b' n' (pjs J k)
  | PMemRespell b lo hi b' d k => PMemRespell b lo hi b' d (pjs J k)
  | PSrlSplit r s k => PSrlSplit r s (pjs J k)
  | PAndRange r logc ub k => PAndRange r logc ub (pjs J k)
  | PAndRangeR r logc rs k => PAndRangeR r logc rs (pjs J k)
  | PSrlSplitAll r s k => PSrlSplitAll r s (pjs J k)
  | PFdHavoc lo hi k => PFdHavoc lo hi (pjs J k)
  | PFreshCellK b n k => PFreshCellK b n (pjs J k)
  | PVisPerm perm k => PVisPerm perm (pjs J k)
  | PHandoffM m => p
  | PFdRespell len off k => PFdRespell len off (pjs J k)
  | PDisjNth b1 n1 i k => PDisjNth b1 n1 i (pjs J k)
  | PMmapInS a b c => PMmapInS (pjs J a) (pjs J b) (pjs J c)
  end.

Record mc_out := MCO { mc_log : list (Z * Z * Z * Z); mc_holes : list (nat * acs); mc_joins : list (nat * acs);
                       mc_shape : option shape }.

(* The entry after an arrival [cs] at an entry already replaced in this run ([seen]) or not. *)
Definition mc_next (seen : bool) (old : option acs) (cs : acs) : acs :=
  match (if seen then old else None) with
  | Some o => mc_meet o cs
  | None => match old with Some o => mc_clean_keep o cs | None => mc_clean cs end
  end.

Section MCol.
  (* [chk HS p]: the node's own check (its image, r, class, fuel and start state fixed), with hole table HS. *)
  Variable chk : (nat -> option acs) -> plan -> cres.
  Variable p : plan.
  Fixpoint mc_loop (n : nat) (H J : list (nat * acs)) (RH RJ : list nat) (log : list (Z * Z * Z * Z)) : mc_out :=
    match n with
    | O => MCO (rev log) H J None
    | S n' =>
      match chk (tlook H) (pjs J p) with
      | COk s => MCO (rev ((0, 0, 0, 0) :: log)) H J (Some s)
      | CErr c w cs =>
          let row := (c, s_pc (a_ss cs), mc_tag w, Z.of_N (nxt cs)) in
          if (Z.eqb c 3 || Z.eqb c 4)%bool then
            match w with
            | PHandoff h =>
                mc_loop n' (tupd H h (mc_next (existsb (Nat.eqb h) RH) (tlook H h) cs)) J (h :: RH) RJ (row :: log)
            | PMerge j =>
                mc_loop n' H (tupd J j (mc_next (existsb (Nat.eqb j) RJ) (tlook J j) cs)) RH (j :: RJ) (row :: log)
            | _ => MCO (rev (row :: log)) H J None
            end
          else MCO (rev (row :: log)) H J None
      end
    end.
End MCol.

(* [pfp p]: a fingerprint of the plan [p], hashed modulo 2^61 - 1 from its constructors, its sub-plans and the sum
   of each run's stops; no other argument is hashed, so two plans can share one. The tree collectors
   ([TreeColA.runnode], [TreeColB.runnode]) record it in a node's log row to identify the plan. *)
Fixpoint pfp (p : plan) : Z :=
  match p with
  | PRun stops k => Z.modulo ((((1) * 1000003 + pfp k)) * 1000003 + fold_left Z.add stops 0) 2305843009213693951
  | PSplit e mid k1 k2 => Z.modulo ((((2) * 1000003 + pfp k1)) * 1000003 + pfp k2) 2305843009213693951
  | PCase2 e mid k1 k2 => Z.modulo ((((3) * 1000003 + pfp k1)) * 1000003 + pfp k2) 2305843009213693951
  | PCaseDisj b1 b2 k1 k2 => Z.modulo ((((4) * 1000003 + pfp k1)) * 1000003 + pfp k2) 2305843009213693951
  | PShDisj b1 n1 b2 n2 k => Z.modulo ((5) * 1000003 + pfp k) 2305843009213693951
  | PContra => Z.modulo 6 2305843009213693951
  | PFact K k => Z.modulo ((7) * 1000003 + pfp k) 2305843009213693951
  | PJoin b off n k => Z.modulo ((8) * 1000003 + pfp k) 2305843009213693951
  | PForget ixs k => Z.modulo ((9) * 1000003 + pfp k) 2305843009213693951
  | PDropRange b n k => Z.modulo ((10) * 1000003 + pfp k) 2305843009213693951
  | PGcKeep ws k => Z.modulo ((11) * 1000003 + pfp k) 2305843009213693951
  | PBump m k => Z.modulo ((12) * 1000003 + pfp k) 2305843009213693951
  | PHavoc rs k => Z.modulo ((13) * 1000003 + pfp k) 2305843009213693951
  | PHavocBig K k => Z.modulo ((14) * 1000003 + pfp k) 2305843009213693951
  | PFresh r logc base k => Z.modulo ((15) * 1000003 + pfp k) 2305843009213693951
  | PSys y k => Z.modulo ((16) * 1000003 + pfp k) 2305843009213693951
  | PMmap ka kb => Z.modulo ((((17) * 1000003 + pfp ka)) * 1000003 + pfp kb) 2305843009213693951
  | PMmapIn a b c => Z.modulo ((((((18) * 1000003 + pfp a)) * 1000003 + pfp b)) * 1000003 + pfp c) 2305843009213693951
  | PMprotect a b => Z.modulo ((((19) * 1000003 + pfp a)) * 1000003 + pfp b) 2305843009213693951
  | PBrk2 a b => Z.modulo ((((20) * 1000003 + pfp a)) * 1000003 + pfp b) 2305843009213693951
  | PMunmap2 a b => Z.modulo ((((21) * 1000003 + pfp a)) * 1000003 + pfp b) 2305843009213693951
  | PX x args k => Z.modulo ((22) * 1000003 + pfp k) 2305843009213693951
  | PExt id args k => Z.modulo ((23) * 1000003 + pfp k) 2305843009213693951
  | PEmit id args k => Z.modulo ((24) * 1000003 + pfp k) 2305843009213693951
  | PExt2 id args k1 k2 => Z.modulo ((((25) * 1000003 + pfp k1)) * 1000003 + pfp k2) 2305843009213693951
  | PLoop J0 N inv body k => Z.modulo ((((26) * 1000003 + pfp body)) * 1000003 + pfp k) 2305843009213693951
  | PNext => Z.modulo 27 2305843009213693951
  | PHandoff h => Z.modulo 28 2305843009213693951
  | PExit => Z.modulo 29 2305843009213693951
  | PSpin => Z.modulo 30 2305843009213693951
  | PFog i sz k => Z.modulo ((31) * 1000003 + pfp k) 2305843009213693951
  | PFogNew i sz k => Z.modulo ((32) * 1000003 + pfp k) 2305843009213693951
  | PGhost b n k => Z.modulo ((33) * 1000003 + pfp k) 2305843009213693951
  | PUnvis b n k => Z.modulo ((34) * 1000003 + pfp k) 2305843009213693951
  | PHavocBrk lo hi k => Z.modulo ((35) * 1000003 + pfp k) 2305843009213693951
  | PIntro lo hi k => Z.modulo ((36) * 1000003 + pfp k) 2305843009213693951
  | PDiamond joinpc rs k => Z.modulo ((37) * 1000003 + pfp k) 2305843009213693951
  | PRename m k => Z.modulo ((38) * 1000003 + pfp k) 2305843009213693951
  | PCompact k => Z.modulo ((39) * 1000003 + pfp k) 2305843009213693951
  | PVia j js lo karms k => Z.modulo ((((40) * 1000003 + pfp karms)) * 1000003 + pfp k) 2305843009213693951
  | PMerge j => Z.modulo 41 2305843009213693951
  | PAbstractCell b n k => Z.modulo ((42) * 1000003 + pfp k) 2305843009213693951
  | PHavocWords bs k => Z.modulo ((43) * 1000003 + pfp k) 2305843009213693951
  | PRespell r e k => Z.modulo ((44) * 1000003 + pfp k) 2305843009213693951
  | PMmapInH a b c => Z.modulo ((((((45) * 1000003 + pfp a)) * 1000003 + pfp b)) * 1000003 + pfp c) 2305843009213693951
  | PCaseDisjJ b1 b2 joinpc rs k => Z.modulo ((46) * 1000003 + pfp k) 2305843009213693951
  | PCaseP k1 k2 => Z.modulo ((((47) * 1000003 + pfp k1)) * 1000003 + pfp k2) 2305843009213693951
  | PCaseNJ e cuts joinpc rs ws k => Z.modulo ((48) * 1000003 + pfp k) 2305843009213693951
  | PVisAbsorb b n k => Z.modulo ((49) * 1000003 + pfp k) 2305843009213693951
  | PFreshCell b n k => Z.modulo ((50) * 1000003 + pfp k) 2305843009213693951
  | PVisSplit b n d k => Z.modulo ((51) * 1000003 + pfp k) 2305843009213693951
  | PVisHead b m L k => Z.modulo ((52) * 1000003 + pfp k) 2305843009213693951
  | PUnvisHead b m k => Z.modulo ((53) * 1000003 + pfp k) 2305843009213693951
  | PGhostDedup k => Z.modulo ((54) * 1000003 + pfp k) 2305843009213693951
  | PHavocBrkP lo hi k => Z.modulo ((55) * 1000003 + pfp k) 2305843009213693951
  | PKeep ws vs k => Z.modulo ((56) * 1000003 + pfp k) 2305843009213693951
  | PFactMem K k => Z.modulo ((57) * 1000003 + pfp k) 2305843009213693951
  | PVisRespell b n b' n' k => Z.modulo ((58) * 1000003 + pfp k) 2305843009213693951
  | PMapRespell b n b' n' k => Z.modulo ((59) * 1000003 + pfp k) 2305843009213693951
  | PMemRespell b lo hi b' d k => Z.modulo ((60) * 1000003 + pfp k) 2305843009213693951
  | PSrlSplit r s k => Z.modulo ((61) * 1000003 + pfp k) 2305843009213693951
  | PAndRange r logc ub k => Z.modulo ((62) * 1000003 + pfp k) 2305843009213693951
  | PAndRangeR r logc rs k => Z.modulo ((63) * 1000003 + pfp k) 2305843009213693951
  | PSrlSplitAll r s k => Z.modulo ((64) * 1000003 + pfp k) 2305843009213693951
  | PFdHavoc lo hi k => Z.modulo ((65) * 1000003 + pfp k) 2305843009213693951
  | PFreshCellK b n k => Z.modulo ((66) * 1000003 + pfp k) 2305843009213693951
  | PVisPerm perm k => Z.modulo ((67) * 1000003 + pfp k) 2305843009213693951
  | PHandoffM m => Z.modulo 68 2305843009213693951
  | PFdRespell len off k => Z.modulo ((69) * 1000003 + pfp k) 2305843009213693951
  | PDisjNth b1 n1 i k => Z.modulo ((70) * 1000003 + pfp k) 2305843009213693951
  | PMmapInS a b c => Z.modulo ((((((71) * 1000003 + pfp a)) * 1000003 + pfp b)) * 1000003 + pfp c) 2305843009213693951
  end.

(* MANY NODES, ONE TABLE. A template is shared by every node that hands off to its hole (TO_asan: ArgR2's node,
   ArgR3's four, ArgR4's), so it must be collected over ALL their arrivals: one node's arrival carries that node's
   class facts (ArgR2's root class 2 pins V_L1 = EVar 7 to [4096, 131071], AsanMainLib.look_L1) and a shared child
   plan cannot start from it (from an ArgR2-only template the leaf's EVar 7 <= 63 branches
   take ASan's slow path at 0x470fc and reach the region check with size 1). [chkn i HS] is node i's check under
   hole table HS. Each round checks the nodes in order; the first refusal or missing entry at a hole replaces or
   meets that entry (as in [mc_loop]) and the round restarts. Joins are not collected here (the plans it is used
   on carry none); any other refusal stops. Rows: (node, code, pc, tag); a final (-1, 0, 0, 0) = every node COk. *)
Record mm_out := MMO { mm_log : list (Z * Z * Z * Z); mm_holes : list (nat * acs); mm_ok : bool }.
Section MMulti.
  Variable chkn : nat -> (nat -> option acs) -> cres.
  Fixpoint mm_first (ns : list nat) (H : list (nat * acs)) : option (nat * Z * plan * acs) :=
    match ns with
    | [] => None
    | i :: ns' => match chkn i (tlook H) with COk _ => mm_first ns' H | CErr c w cs => Some (i, c, w, cs) end
    end.
  Fixpoint mm_loop (ns : list nat) (n : nat) (H : list (nat * acs)) (RH : list nat) (log : list (Z * Z * Z * Z)) : mm_out :=
    match n with
    | O => MMO (rev log) H false
    | S n' =>
      match mm_first ns H with
      | None => MMO (rev ((-1, 0, 0, 0) :: log)) H true
      | Some (i, c, w, cs) =>
          let row := (Z.of_nat i, c, s_pc (a_ss cs), mc_tag w) in
          match w with
          | PHandoff h =>
              if (Z.eqb c 3 || Z.eqb c 4)%bool
              then mm_loop ns n' (tupd H h (mc_next (existsb (Nat.eqb h) RH) (tlook H h) cs)) (h :: RH) (row :: log)
              else MMO (rev (row :: log)) H false
          | _ => MMO (rev (row :: log)) H false
          end
      end
    end.
End MMulti.

(* MANY NODES, ONE HOLE TABLE, JOINS PER PLAN. As [mm_loop], and a refused or missing join ([PMerge j], code 3/4)
   at node i replaces or meets the join entry j of node i's PLAN ([pid i]), read back into that plan by [pjs]. Joins
   are keyed by plan (key pid * 100000 + j) because join indices are local to a plan (two plans may both say
   [PVia 0]), while nodes that run the same plan from the same template share its joins. [chkn i HS f] is node i's
   check under hole table HS with its plan rewritten by f. Rows and the final (-1, 0, 0, 0) as [mm_loop]. *)
Record mmj_out := MMJO { mmj_log : list (Z * Z * Z * Z); mmj_holes : list (nat * acs); mmj_joins : list (nat * acs);
                         mmj_ok : bool }.
Definition jkey (i j : nat) : nat := i * 100000 + j.
Fixpoint jof (J : list (nat * acs)) (i : nat) : list (nat * acs) :=
  match J with
  | [] => []
  | (k, s) :: J' => if Nat.eqb (Nat.div k 100000) i then (Nat.modulo k 100000, s) :: jof J' i else jof J' i
  end.
Section MMJ.
  Variable chkn : nat -> (nat -> option acs) -> (plan -> plan) -> cres.
  Variable pid : nat -> nat.
  (* The first node whose refusal is collectable (code 3/4 at a hole or a join); nodes refused anywhere else are
     skipped and returned as rows, so one stuck node does not stop the collection of the others. *)
  Definition mmj_coll (c : Z) (w : plan) : bool :=
    (Z.eqb c 3 || Z.eqb c 4)%bool && match w with PHandoff _ | PMerge _ => true | _ => false end.
  Fixpoint mmj_first (ns : list nat) (H J : list (nat * acs)) (stuck : list (Z * Z * Z * Z)) :
      option (nat * Z * plan * acs) * list (Z * Z * Z * Z) :=
    match ns with
    | [] => (None, rev stuck)
    | i :: ns' => match chkn i (tlook H) (pjs (jof J (pid i))) with
                  | COk _ => mmj_first ns' H J stuck
                  | CErr c w cs => if mmj_coll c w then (Some (i, c, w, cs), [])
                                   else mmj_first ns' H J ((Z.of_nat i, c, s_pc (a_ss cs), mc_tag w) :: stuck)
                  end
    end.
  (* Rows: (node, code, pc, tag) per collection step; at the end the stuck nodes' rows, then (-1, 0, 0, 0).
     [mmj_ok] = every node COk. *)
  Fixpoint mmj_loop (ns : list nat) (n : nat) (H J : list (nat * acs)) (RH RJ : list nat) (log : list (Z * Z * Z * Z)) : mmj_out :=
    match n with
    | O => MMJO (rev log) H J false
    | S n' =>
      match mmj_first ns H J [] with
      | (None, st) => MMJO (rev log ++ st ++ [(-1, 0, 0, 0)]) H J (match st with [] => true | _ => false end)
      | (Some (i, c, w, cs), _) =>
          let row := (Z.of_nat i, c, s_pc (a_ss cs), mc_tag w) in
          match w with
          | PHandoff h => mmj_loop ns n' (tupd H h (mc_next (existsb (Nat.eqb h) RH) (tlook H h) cs)) J (h :: RH) RJ (row :: log)
          | PMerge j => let k := jkey (pid i) j in
              mmj_loop ns n' H (tupd J k (mc_next (existsb (Nat.eqb k) RJ) (tlook J k) cs)) RH (k :: RJ) (row :: log)
          | _ => MMJO (rev (row :: log)) H J false
          end
      end
    end.
End MMJ.
