(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3: the start-up chain's hand-off tables computed in the build from each level's start state (pc_collect, pc_meet) and the variable map cg_map that runs a level's recorded plan from them, with the join pc_join for a hand-off reached twice, after openssl/punycode's Start/PlanCoGen.v, and the piece intersections of this unit's Common/AsanPlan.v (hxm_isect, hxm_zeros) for its image and zero pieces. *)
(* The start-up chain's hand-off tables, COMPUTED from each level's start state, and the variable map that lets a
   level's plan run unchanged from a regenerated predecessor.

   [pc_collect chk] runs [chk T] (a level's certificate call over the hole table [T]) until it returns [COk]. The
   table starts empty; [CErr 4] at [PHandoff 0] records the arriving state; [CErr 3] there replaces it by its meet
   with the arriving state (the knowledge facts common to both; the first arrival's registers, maps and pc). Any
   other stop ends the collection. A table returned with [COk] is therefore exactly one [check] accepts for this start
   state and plan; nothing about it is assumed, the level's certificate re-checks it.  [pc_collect_j] is the same
   collector with the second rule [pc_join] at [CErr 3], for a level whose two arrivals hold different literals in
   some memory words (see [pc_join]).

   [cg_map old new] aligns a recorded state [old] with a computed one [new] structurally (memory maps, registers,
   vis, ghost, brk, then knowledge facts) and returns a [PRename] map, completed to a permutation of [new]'s live
   variables, that puts [new] into [old]'s numbering. A level whose plan was generated against [old] runs from [new]
   as [PRename (cg_map old new) plan]; a wrong map can only make that level's [check] fail. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition pc_clean (c : acs) : acs :=
  let s := a_ss c in
  ACS (SSR (s_pc s) (s_regs s) [] (s_know s) (s_next s) (s_resv s)) (a_maps c) (a_totsz c) (a_ylo c) (a_eager c)
      (a_vis c) (a_ghost c) (a_abytes c) (a_brk c) (a_fd c) (a_tidset c).
Definition pc_meet (c0 c : acs) : acs :=
  let s := a_ss c0 in
  ACS (SSR (s_pc s) (s_regs s) [] (List.filter (fun K => existsb (kentry_eqb K) (kn c)) (s_know s)) (s_next s) (s_resv s))
      (a_maps c0) (Z.max (a_totsz c0) (a_totsz c)) (Z.min (a_ylo c0) (a_ylo c)) (Z.max (a_eager c0) (a_eager c))
      (a_vis c0) (a_ghost c0) (Z.max (a_abytes c0) (a_abytes c)) (a_brk c0) (a_fd c0) (a_tidset c0).
Definition pc_tbl (t : option acs) (h : nat) : option acs := match t with Some c => if Nat.eqb h 0 then Some c else None | None => None end.
Definition pc_tag (p : plan) : Z := match p with PHandoff h => 200 + Z.of_nat h | PRun _ _ => 1 | PX _ _ _ => 2 | PExt i _ _ => 400 + Z.of_nat i | _ => 0 end.
(* one row per round: (code, pc, node tag, nxt, number of knowledge facts in the arriving state) *)
Definition pc_row (r : cres) : Z * Z * Z * Z * Z :=
  match r with
  | COk _ => (0, 0, 0, 0, 0)
  | CErr c w cs => (c, s_pc (a_ss cs), pc_tag w, Z.of_nat (nxt cs), Z.of_nat (length (kn cs)))
  end.
Record pc_out := PCO { po_tab : option acs; po_log : list (Z * Z * Z * Z * Z); po_shape : option shape }.
Fixpoint pc_go_by (jn : acs -> acs -> acs) (chk : (nat -> option acs) -> cres) (n : nat) (t : option acs)
         (log : list (Z * Z * Z * Z * Z)) : pc_out :=
  match n with
  | O => PCO t (rev log) None
  | S n' =>
    let r := chk (pc_tbl t) in
    match r with
    | COk s => PCO t (rev (pc_row r :: log)) (Some s)
    | CErr c (PHandoff 0) cs =>
        if Z.eqb c 4 then pc_go_by jn chk n' (Some (pc_clean cs)) (pc_row r :: log)
        else if Z.eqb c 3 then
          match t with
          | Some c0 => pc_go_by jn chk n' (Some (jn c0 cs)) (pc_row r :: log)
          | None => PCO t (rev (pc_row r :: log)) None
          end
        else PCO t (rev (pc_row r :: log)) None
    | _ => PCO t (rev (pc_row r :: log)) None
    end
  end.
Definition pc_go : ((nat -> option acs) -> cres) -> nat -> option acs -> list (Z * Z * Z * Z * Z) -> pc_out :=
  pc_go_by pc_meet.
Definition pc_collect (chk : (nat -> option acs) -> cres) : pc_out := pc_go chk 8 None [].

(* [pc_join A c0 c]: the second rule for a hand-off reached twice, for a level whose two arrivals hold different
   literals in some memory words (openssl/pem and openssl/punycode level 3: the ASan stack-depot count is 3 on the
   first arrival and 2 on the second, and the words derived from it differ with it).  [pc_meet] drops every such
   word.  This rule keeps, besides the meet,
   - each fact of one arrival that the other arrival passes under the hand-off's own test on one fact
     ([kn_incl1_x A], the test [entails_x] applies, over the level's image table [A]),
   - the intersections of the two arrivals' image pieces ([KImg]) and of their zero pieces over the same base
     ([KZero]): that test accepts an image or zero piece only inside ONE piece of the state, so where the two
     arrivals cut the same range at different words (openssl/pem level 3: the stack-depot hash table, cut at the
     first arrival's bucket in one and at the second's in the other), neither arrival's own pieces pass the other,
     and the range between the two cuts would be lost; each intersection lies inside a piece of each arrival, and
   - for the words both arrivals state as different literals x (first arrival) and y (second): one fresh variable
     v (numbered above both arrivals' counters) standing for the BASE word, and every such word as the affine
     function of v through the two arrivals' values when the difference divides exactly, each with the range
     [min x y, max x y] of its values.  The base is the word whose two values are closest (the smallest
     |x - y|); among those, a word at a literal address before one at a symbolic address, and the lowest literal
     address first (so the choice does not depend on the order of the arrivals' fact lists); then list order.
   Every fact is a fact of each arrival once v is the base word's value in it, which [entails_x] infers from that
   word (it is stated as the bare [EVar v]); the level's certificate re-checks both arrivals against the table,
   nothing is assumed.  (The rule is openssl/punycode's Start/PlanCoGen.v [pc_join] with the base word chosen as
   above instead of the first word, and with the piece intersections added.) *)
Definition pj_lit (k : list kentry) (a : saddr) (w : nat) : option Z :=
  match hx_cell k a w with Some (ELit z) => if (Z.leb 0 z && Z.ltb z (2 ^ 64))%bool then Some z else None | _ => None end.
Fixpoint pj_diffs (k0 k : list kentry) (seen : list (saddr * nat)) : list (saddr * nat * Z * Z) :=
  match k0 with
  | [] => []
  | KWord a w _ :: r =>
      if existsb (fun p => (saddr_eqb (fst p) a && Nat.eqb (snd p) w)%bool) seen then pj_diffs r k seen
      else match pj_lit k0 a w, pj_lit k a w with
           | Some x, Some y =>
               if Z.eqb x y then pj_diffs r k ((a, w) :: seen) else (a, w, x, y) :: pj_diffs r k ((a, w) :: seen)
           | _, _ => pj_diffs r k ((a, w) :: seen)
           end
  | _ :: r => pj_diffs r k seen
  end.
Definition pj_addr (a : saddr) : option Z := match a_base a with ELit z => Some (z + a_off a) | _ => None end.
Definition pj_better (d b : saddr * nat * Z * Z) : bool :=
  let '(a, _, x, y) := d in
  let '(a', _, x', y') := b in
  if Z.ltb (Z.abs (x - y)) (Z.abs (x' - y')) then true
  else if Z.eqb (Z.abs (x - y)) (Z.abs (x' - y')) then
    match pj_addr a, pj_addr a' with
    | Some p, Some q => Z.ltb p q
    | Some _, None => true
    | _, _ => false
    end
  else false.
Fixpoint pj_best (ds : list (saddr * nat * Z * Z)) (best : option (saddr * nat * Z * Z)) : option (saddr * nat * Z * Z) :=
  match ds with
  | [] => best
  | d :: r => match best with
              | Some b => pj_best r (if pj_better d b then Some d else best)
              | None => pj_best r (Some d)
              end
  end.
Definition pj_base (ds : list (saddr * nat * Z * Z)) : option (Z * Z) :=
  match pj_best ds None with Some (_, _, x, y) => Some (x, y) | None => None end.
Definition pj_gen (v : nat) (ds : list (saddr * nat * Z * Z)) : list kentry :=
  match pj_base ds with
  | None => []
  | Some (xk, yk) =>
      let dk := xk - yk in
      List.flat_map (fun d => let '(a, w, x, y) := d in
                       if Z.eqb ((x - y) mod dk) 0 then
                         let s := (x - y) / dk in
                         let e := eadd (escale s (EVar v)) (ELit (y - s * yk)) in
                         [KWord a w e; KRange e (Z.min x y) (Z.max x y)]
                       else []) ds
  end.
Definition pj_isect (p q : Z * Z) : list (Z * Z) :=
  let lo := Z.max (fst p) (fst q) in let hi := Z.min (snd p) (snd q) in if Z.ltb lo hi then [(lo, hi)] else [].
Definition pj_imgs (k : list kentry) : list (Z * Z) :=
  List.flat_map (fun K => match K with KImg lo hi => [(lo, hi)] | _ => [] end) k.
Definition pj_zeros (k : list kentry) : list (expr * Z * Z) :=
  List.flat_map (fun K => match K with
                          | KZero (SA b o) (ELit n) => if (Z.ltb 0 n && Z.ltb n two64)%bool then [(b, o, o + n)] else []
                          | _ => [] end) k.
Definition pj_cover (k0 k : list kentry) : list kentry :=
  let i1 := pj_imgs k in
  let z1 := pj_zeros k in
  List.flat_map (fun p => List.flat_map (fun q => List.map (fun r => KImg (fst r) (snd r)) (pj_isect p q)) i1) (pj_imgs k0)
  ++ List.flat_map (fun z => let '(b, o, e) := z in
                     List.flat_map (fun z' => let '(b', o', e') := z' in
                                      if expr_eqb b b' then List.map (fun r => KZero (SA b (fst r)) (ELit (snd r - fst r))) (pj_isect (o, e) (o', e'))
                                      else []) z1) (pj_zeros k0).
Fixpoint pj_new (kept : list kentry) (xs : list kentry) : list kentry :=
  match xs with
  | [] => []
  | K :: r => if existsb (kentry_eqb K) kept then pj_new kept r else K :: pj_new (K :: kept) r
  end.
Definition pc_join (A : atable) (c0 c : acs) : acs :=
  let m := pc_meet c0 c in
  let inm K := existsb (kentry_eqb K) (kn m) in
  let keep0 := List.filter (fun K => (negb (inm K) && kn_incl1_x A c K)%bool) (kn c0) in
  let keep1 := List.filter (fun K => (negb (inm K) && negb (existsb (kentry_eqb K) keep0) && kn_incl1_x A c0 K)%bool) (kn c) in
  let v := Nat.max (nxt c0) (nxt c) in
  let gen := pj_gen v (pj_diffs (kn c0) (kn c) []) in
  let cov := pj_new (kn m ++ keep0 ++ keep1) (pj_cover (kn c0) (kn c)) in
  let s := a_ss m in
  ACS (SSR (s_pc s) (s_regs s) [] (kn m ++ keep0 ++ keep1 ++ cov ++ gen) (match gen with [] => v | _ => S v end) (s_resv s))
      (a_maps m) (a_totsz m) (a_ylo m) (a_eager m) (a_vis m) (a_ghost m) (a_abytes m) (a_brk m) (a_fd m) (a_tidset m).
Definition pc_collect_j (A : atable) (chk : (nat -> option acs) -> cres) : pc_out := pc_go_by (pc_join A) chk 8 None [].
(* the level's new hand-off state: the collected one if the level reached COk, else the recorded one, so that the
   next level is still measured from SOMETHING; the summary says which *)
Definition pc_next (r : pc_out) (old : acs) : acs := match po_shape r, po_tab r with Some _, Some c => c | _, _ => old end.
Definition pc_ok (r : pc_out) : bool := match po_shape r with Some _ => true | None => false end.

Fixpoint cg_lk (s : list (nat * nat)) (a : nat) : option nat :=
  match s with [] => None | (x, y) :: r => if Nat.eqb x a then Some y else cg_lk r a end.
Fixpoint cg_rlk (s : list (nat * nat)) (b : nat) : option nat :=
  match s with [] => None | (x, y) :: r => if Nat.eqb y b then Some x else cg_rlk r b end.

(* extend the partial bijection [s] (old -> new) so that [a] (old) and [b] (new) are equal under it *)
Fixpoint cg_ue (s : list (nat * nat)) (a b : expr) {struct a} : option (list (nat * nat)) :=
  match a, b with
  | ELit x, ELit y => if Z.eqb x y then Some s else None
  | EVar x, EVar y =>
      match cg_lk s x with
      | Some y' => if Nat.eqb y y' then Some s else None
      | None => match cg_rlk s y with Some _ => None | None => Some ((x, y) :: s) end
      end
  | EAlu o a1 a2, EAlu o' b1 b2 | EAluw o a1 a2, EAluw o' b1 b2 =>
      if aluop_eqb o o' then match cg_ue s a1 b1 with Some s1 => cg_ue s1 a2 b2 | None => None end else None
  | EMd o a1 a2, EMd o' b1 b2 | EMdw o a1 a2, EMdw o' b1 b2 =>
      if mulop_eqb o o' then match cg_ue s a1 b1 with Some s1 => cg_ue s1 a2 b2 | None => None end else None
  | EExt x l n e, EExt x' l' n' e' =>
      if (Bool.eqb x x' && Nat.eqb l l' && Nat.eqb n n')%bool then cg_ue s e e' else None
  | EBlob x k i n, EBlob x' k' i' n' =>
      if (Bool.eqb x x' && Nat.eqb k k' && Z.eqb i i' && Nat.eqb n n')%bool then Some s else None
  | _, _ => None
  end.

Definition cg_ua (s : list (nat * nat)) (a b : saddr) : option (list (nat * nat)) :=
  if Z.eqb (a_off a) (a_off b) then cg_ue s (a_base a) (a_base b) else None.
Definition cg_bind (o : option (list (nat * nat))) (f : list (nat * nat) -> option (list (nat * nat))) :=
  match o with Some s => f s | None => None end.

Definition cg_uk (s : list (nat * nat)) (K K' : kentry) : option (list (nat * nat)) :=
  match K, K' with
  | KWord a w v, KWord a' w' v' => if Nat.eqb w w' then cg_bind (cg_ua s a a') (fun s => cg_ue s v v') else None
  | KZero a n, KZero a' n' | KWr a n, KWr a' n' | KUnk a n, KUnk a' n' =>
      cg_bind (cg_ua s a a') (fun s => cg_ue s n n')
  | KBlob a n k, KBlob a' n' k' => if Nat.eqb k k' then cg_bind (cg_ua s a a') (fun s => cg_ue s n n') else None
  | KImg lo hi, KImg lo' hi' => if (Z.eqb lo lo' && Z.eqb hi hi')%bool then Some s else None
  | KAlign e m, KAlign e' m' => if Z.eqb m m' then cg_ue s e e' else None
  | KRange e lo hi, KRange e' lo' hi' => if (Z.eqb lo lo' && Z.eqb hi hi')%bool then cg_ue s e e' else None
  | KDisj a1 n1 a2 n2, KDisj a1' n1' a2' n2' =>
      cg_bind (cg_ua s a1 a1') (fun s => cg_bind (cg_ue s n1 n1') (fun s => cg_bind (cg_ua s a2 a2') (fun s => cg_ue s n2 n2')))
  | KFill a n c, KFill a' n' c' => if Z.eqb c c' then cg_bind (cg_ua s a a') (fun s => cg_ue s n n') else None
  | _, _ => None
  end.

(* pairwise, in order; a pair that does not unify is skipped (the state lost or reworded that item) *)
Fixpoint cg_pairs {T} (u : list (nat * nat) -> T -> T -> option (list (nat * nat))) (s : list (nat * nat))
         (xs ys : list T) : list (nat * nat) :=
  match xs, ys with
  | x :: xs', y :: ys' => match u s x y with Some s' => cg_pairs u s' xs' ys' | None => cg_pairs u s xs' ys' end
  | _, _ => s
  end.
(* each old fact against the first new fact it unifies with under the current [s] *)
Fixpoint cg_first (s : list (nat * nat)) (K : kentry) (ys : list kentry) : option (list (nat * nat)) :=
  match ys with [] => None | y :: r => match cg_uk s K y with Some s' => Some s' | None => cg_first s K r end end.
Fixpoint cg_facts (s : list (nat * nat)) (xs ys : list kentry) (miss : nat) : list (nat * nat) * nat :=
  match xs with
  | [] => (s, miss)
  | K :: r => match cg_first s K ys with Some s' => cg_facts s' r ys miss | None => cg_facts s r ys (S miss) end
  end.
Definition cg_um (s : list (nat * nat)) (m m' : amap) : option (list (nat * nat)) :=
  if mkind_eqb (am_kind m) (am_kind m') then cg_bind (cg_ue s (am_base m) (am_base m')) (fun s => cg_ue s (am_len m) (am_len m')) else None.
Definition cg_up (s : list (nat * nat)) (p p' : expr * expr) : option (list (nat * nat)) :=
  cg_bind (cg_ue s (fst p) (fst p')) (fun s => cg_ue s (snd p) (snd p')).

(* sigma (old -> new) and the number of old facts with no partner *)
Definition cg_align (old new : acs) : list (nat * nat) * nat :=
  let s0 := List.map (fun i => (i, i)) (seq 0 NX0) in      (* the launch's variables are the same on both sides *)
  let s1 := cg_pairs cg_um s0 (a_maps old) (a_maps new) in
  let s2 := cg_pairs cg_ue s1 (s_regs (a_ss old)) (s_regs (a_ss new)) in
  let s3 := cg_pairs cg_up s2 (a_vis old) (a_vis new) in
  let s4 := cg_pairs cg_up s3 (a_ghost old) (a_ghost new) in
  let s5 := match cg_ue s4 (a_brk old) (a_brk new) with Some s => s | None => s4 end in
  cg_facts s5 (kn old) (kn new) 0.

(* the PRename map new -> old over the NEW state's live variables at or above NX0: matched ones go to their old
   number, the rest to fresh numbers from [fresh0] up (above every old number), so the map is injective *)
Fixpoint cg_complete (sig : list (nat * nat)) (live : list nat) (fresh : nat) : list (nat * nat) :=
  match live with
  | [] => []
  | v :: r => match cg_rlk sig v with
              | Some o => (v, o) :: cg_complete sig r fresh
              | None => (v, fresh) :: cg_complete sig r (S fresh)
              end
  end.
Definition cg_map (old new : acs) : list (nat * nat) :=
  let sig := fst (cg_align old new) in
  cg_complete sig (csvars_fo NX0 new) (Nat.max (nxt old) (nxt new)).
