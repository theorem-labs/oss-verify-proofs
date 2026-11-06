(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith PArith NArith List Bool Lia.
From Stdlib Require Import PrimInt63.
From Stdlib Require PrimString.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive pfact : Set :=
| FGe (e : expr)                          (* [comment removed for export] *)
| FSep (a n b k : expr)                   (* [comment removed for export] *)
| FSep0 (z a n b k : expr)                (* [comment removed for export] *)
| FAl (a : expr) (k : N)                  (* [comment removed for export] *)
| FCr (a n : expr)                        (* [comment removed for export] *)
| FShb (k : positive) (c : expr) (oa on : expr)
    (* [comment removed for export] *)
(* [comment removed for export] *)
| FLe (a b : expr)                        (* [comment removed for export] *)
| FLt (a b : expr)                        (* [comment removed for export] *)
| FEq (a b : expr)                        (* [comment removed for export] *)
| FOr2 (l1 r1 l2 r2 : expr)               (* [comment removed for export] *)
| FOr3z (z l1 r1 l2 r2 : expr)            (* [comment removed for export] *)
(* [comment removed for export] *)
| FProp (j : nat) (args : list expr).

Fixpoint ivs_eqb (a b : list (expr * expr)) : bool :=
  match a, b with
  | [], [] => true
  | (x1, y1) :: a', (x2, y2) :: b' => expr_eqb x1 x2 && expr_eqb y1 y2 && ivs_eqb a' b'
  | _, _ => false
  end.

Fixpoint exprs_eqb (a b : list expr) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => expr_eqb x y && exprs_eqb a' b' | _, _ => false end.

Definition pfact_eqb (x y : pfact) : bool :=
  match x, y with
  | FGe a, FGe b => expr_eqb a b
  | FSep a n b k, FSep a' n' b' k' => expr_eqb a a' && expr_eqb n n' && expr_eqb b b' && expr_eqb k k'
  | FSep0 z a n b k, FSep0 z' a' n' b' k' =>
      expr_eqb z z' && expr_eqb a a' && expr_eqb n n' && expr_eqb b b' && expr_eqb k k'
  | FAl a k, FAl a' k' => expr_eqb a a' && N.eqb k k'
  | FCr a n, FCr a' n' => expr_eqb a a' && expr_eqb n n'
  | FShb k c oa on, FShb k' c' oa' on' => Pos.eqb k k' && expr_eqb c c' && expr_eqb oa oa' && expr_eqb on on'
  | FLe a b, FLe a' b' => expr_eqb a a' && expr_eqb b b'
  | FLt a b, FLt a' b' => expr_eqb a a' && expr_eqb b b'
  | FEq a b, FEq a' b' => expr_eqb a a' && expr_eqb b b'
  | FOr2 a b c d, FOr2 a' b' c' d' => expr_eqb a a' && expr_eqb b b' && expr_eqb c c' && expr_eqb d d'
  | FOr3z z a b c d, FOr3z z' a' b' c' d' => expr_eqb z z' && expr_eqb a a' && expr_eqb b b' && expr_eqb c c' && expr_eqb d d'
  | FProp j xs, FProp j' xs' => Nat.eqb j j' && exprs_eqb xs xs'
  | _, _ => false
  end.

Fixpoint pf_mem (f : pfact) (l : list pfact) : bool :=
  match l with [] => false | g :: l' => pfact_eqb f g || pf_mem f l' end.

Definition pf_add (f : pfact) (l : list pfact) : list pfact :=
  if pf_mem f l then l else f :: l.

(* [comment removed for export] *)
Definition pf_inter (a b : list pfact) : list pfact := filter (fun f => pf_mem f b) a.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive prop : Set :=
| PGe (e : expr)                          (* [comment removed for export] *)
| PSep (a n b k : expr).                  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition atom_free (a : expr) : list expr :=
  match a with
  | EUv _ => [eatom a; eadd (ELit (two64 - 1)) (emulc (-1) (eatom a))]
  | EOp OLow _ (ELit k) =>
      if Z.leb 0 k then [eatom a; eadd (ELit (2 ^ k - 1)) (emulc (-1) (eatom a))] else []
  | EOp OSx _ (ELit k) =>
      if Z.ltb 0 k then [eadd (eatom a) (ELit (2 ^ (k - 1))); eadd (ELit (2 ^ (k - 1) - 1)) (emulc (-1) (eatom a))] else []
  | EOp OLtu _ _ | EOp OLts _ _ => [eatom a; eadd (ELit 1) (emulc (-1) (eatom a))]
  | EOp OAnd _ (ELit m) =>
      if Z.leb 0 m then [eatom a; eadd (ELit m) (emulc (-1) (eatom a))] else []
  | _ => []
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint expr_mem (e : expr) (l : list expr) : bool :=
  match l with [] => false | x :: l' => expr_eqb e x || expr_mem e l' end.

(* [comment removed for export] *)
Fixpoint atoms_of (e : expr) (acc : list expr) : list expr :=
  match e with
  | ELit _ => acc
  | EAdd a b => atoms_of a (atoms_of b acc)
  | EMulC _ a => atoms_of a acc
  | _ => if expr_mem e acc then acc else e :: acc
  end.

Fixpoint atoms_of_list (l : list expr) (acc : list expr) : list expr :=
  match l with [] => acc | e :: l' => atoms_of_list l' (atoms_of e acc) end.

(* [comment removed for export] *)
Fixpoint pf_pool (pf : list pfact) : list expr :=
  match pf with
  | [] => []
  | FGe e :: pf' => e :: pf_pool pf'
  | _ :: pf' => pf_pool pf'
  end.

Fixpoint flat_map_free (ats : list expr) : list expr :=
  match ats with [] => [] | a :: ats' => atom_free a ++ flat_map_free ats' end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive cert : Set :=
| CFk (l : list (N * Z))                  (* [comment removed for export] *)
| CFkX (cuts : list (list (N * Z) * Z)) (l : list (N * Z))
    (* [comment removed for export] *)
| CSp (j : N) (cl cr : cert)              (* [comment removed for export] *)
| CSp0 (j : N) (c0 cl cr : cert).         (* [comment removed for export] *)

Fixpoint nth_N {A} (l : list A) (n : N) (d : A) : A :=
  match l with
  | [] => d
  | x :: l' => if N.eqb n 0 then x else nth_N l' (N.pred n) d
  end.

Fixpoint fk_sum (pool : list expr) (l : list (N * Z)) : option expr :=
  match l with
  | [] => Some (ELit 0)
  | (i, lam) :: l' =>
      if Z.ltb 0 lam then
        match fk_sum pool l' with
        | Some acc => Some (eadd acc (emulc lam (nth_N pool i (ELit 0))))
        | None => None
        end
      else None
  end.

Definition fk_check (pool : list expr) (l : list (N * Z)) : bool :=
  match fk_sum pool l with
  | Some (ELit c) => Z.ltb c 0
  | _ => false
  end.

(* [comment removed for export] *)
Fixpoint terms_divq (g : Z) (ts : terms) : terms :=
  match ts with [] => [] | (k, a) :: ts' => (k / g, a) :: terms_divq g ts' end.

Fixpoint cut_steps (pool : list expr) (cuts : list (list (N * Z) * Z)) : option (list expr) :=
  match cuts with
  | [] => Some pool
  | (pv, g) :: cuts' =>
      match fk_sum pool pv with
      | Some e =>
          let '(ts, c) := lin_of e in
          if Z.ltb 0 g && forallb (fun t => Z.eqb (fst t mod g) 0) ts
          then cut_steps (pool ++ [of_terms (terms_divq g ts) (c / g)]) cuts'
          else None
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition sep_l (a n b : expr) : expr := eadd b (emulc (-1) (eadd a n)).
Definition sep_r (a b k : expr) : expr := eadd a (emulc (-1) (eadd b k)).

Fixpoint cert_check (pf : list pfact) (pool : list expr) (c : cert) : bool :=
  match c with
  | CFk l => fk_check pool l
  | CFkX cuts l => match cut_steps pool cuts with Some pool' => fk_check pool' l | None => false end
  | CSp j cl cr =>
      match nth_N pf j (FGe (ELit 0)) with
      | FSep a n b k => cert_check pf (sep_l a n b :: pool) cl && cert_check pf (sep_r a b k :: pool) cr
      | _ => false
      end
  | CSp0 j c0 cl cr =>
      match nth_N pf j (FGe (ELit 0)) with
      | FSep0 z a n b k =>
          cert_check pf (z :: emulc (-1) z :: pool) c0
          && cert_check pf (sep_l a n b :: pool) cl && cert_check pf (sep_r a b k :: pool) cr
      | _ => false
      end
  end.

(* [comment removed for export] *)
Fixpoint al_lookup (pf : list pfact) (a : expr) : N :=
  match pf with
  | [] => 0%N
  | FAl b k :: pf' => if expr_eqb a b then N.max k (al_lookup pf' a) else al_lookup pf' a
  | _ :: pf' => al_lookup pf' a
  end.

(* [comment removed for export] *)
Definition align_link (pf : list pfact) (a : expr) : list expr :=
  match a with
  | EZv _ | EUv _ =>
      let e := al_lookup pf a in
      if N.leb 1 e && N.leb e 62 then
        let q := eatom (EOp OShr a (ELit (Z.of_N e))) in
        [eadd (eatom a) (emulc (- 2 ^ Z.of_N e) q); eadd (emulc (2 ^ Z.of_N e) q) (emulc (-1) (eatom a))]
      else []
  | _ => []
  end.

Fixpoint flat_map_align (pf : list pfact) (ats : list expr) : list expr :=
  match ats with [] => [] | a :: ats' => align_link pf a ++ flat_map_align pf ats' end.

(* [comment removed for export] *)
Definition goal_free (a : expr) : list expr :=
  match a with
  | EOp OShr x (ELit k) =>
      if Z.leb 0 k && Z.leb k 62 then
        [eadd x (emulc (- 2 ^ k) (eatom a)); eadd (eadd (emulc (2 ^ k) (eatom a)) (ELit (2 ^ k - 1))) (emulc (-1) x)]
      else []
  (* [comment removed for export] *)
  | EOp OOr x (ELit k) =>
      if Z.leb 0 k then [eadd (eatom a) (emulc (-1) x); eadd (eadd x (ELit k)) (emulc (-1) (eatom a))] else []
  | _ => []
  end.

Fixpoint flat_map_goal_free (ats : list expr) : list expr :=
  match ats with [] => [] | a :: ats' => goal_free a ++ flat_map_goal_free ats' end.

(* [comment removed for export] *)
Fixpoint comm_links (ats all : list expr) : list expr :=
  match ats with
  | [] => []
  | (EOp OMul a b as x) :: ats' =>
      let y := EOp OMul b a in
      if expr_mem y all then eadd (eatom x) (emulc (-1) (eatom y)) :: eadd (eatom y) (emulc (-1) (eatom x)) :: comm_links ats' all
      else comm_links ats' all
  | _ :: ats' => comm_links ats' all
  end.

Definition base_pool (pf : list pfact) (goals : list expr) : list expr :=
  let asserted := pf_pool pf in
  let ats := atoms_of_list (goals ++ asserted) [] in
  map (fun g => eadd (ELit (-1)) (emulc (-1) g)) goals ++ asserted ++ flat_map_free ats ++ flat_map_goal_free (atoms_of_list goals []) ++ flat_map_align pf (atoms_of_list goals [])
  ++ comm_links ats ats.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record cstr := CS { c_ts : terms; c_c : Z; c_pv : list (N * Z) }.

Fixpoint pv_scale (k : Z) (l : list (N * Z)) : list (N * Z) :=
  match l with [] => [] | (i, x) :: l' => (i, k * x) :: pv_scale k l' end.

Fixpoint pv_add (xs : list (N * Z)) : list (N * Z) -> list (N * Z) :=
  match xs with
  | [] => fun ys => ys
  | (i, x) :: xs' =>
      fix go (ys : list (N * Z)) : list (N * Z) :=
        match ys with
        | [] => xs
        | (j, y) :: ys' =>
            match N.compare i j with
            | Lt => (i, x) :: pv_add xs' ys
            | Gt => (j, y) :: go ys'
            | Eq => (i, x + y) :: pv_add xs' ys'
            end
        end
  end.

Fixpoint coeff_of (a : expr) (ts : terms) : Z :=
  match ts with
  | [] => 0
  | (k, b) :: ts' => if expr_eqb a b then k else coeff_of a ts'
  end.

Fixpoint terms_remove (a : expr) (ts : terms) : terms :=
  match ts with
  | [] => []
  | (k, b) :: ts' => if expr_eqb a b then ts' else (k, b) :: terms_remove a ts'
  end.

Definition cstr_comb (kp : Z) (p : cstr) (kn : Z) (n : cstr) : cstr :=
  CS (terms_add (terms_scale kp (c_ts p)) (terms_scale kn (c_ts n)))
     (kp * c_c p + kn * c_c n)
     (pv_add (pv_scale kp (c_pv p)) (pv_scale kn (c_pv n))).

Fixpoint find_contra (cs : list cstr) : option (list (N * Z)) :=
  match cs with
  | [] => None
  | c :: cs' => match c_ts c with
                | [] => if Z.ltb (c_c c) 0 then Some (c_pv c) else find_contra cs'
                | _ => find_contra cs'
                end
  end.

Fixpoint partition3 (a : expr) (cs : list cstr) (pos neg zer : list cstr) : list cstr * list cstr * list cstr :=
  match cs with
  | [] => (pos, neg, zer)
  | c :: cs' =>
      let k := coeff_of a (c_ts c) in
      if Z.ltb 0 k then partition3 a cs' (c :: pos) neg zer
      else if Z.ltb k 0 then partition3 a cs' pos (c :: neg) zer
      else partition3 a cs' pos neg (c :: zer)
  end.

Fixpoint combine_all (a : expr) (pos neg : list cstr) (acc : list cstr) (cap : nat) : option (list cstr) :=
  match pos with
  | [] => Some acc
  | p :: pos' =>
      let kp := coeff_of a (c_ts p) in
      let res := (fix go (neg : list cstr) (acc : list cstr) (cap : nat) : option (list cstr * nat) :=
                    match neg with
                    | [] => Some (acc, cap)
                    | n :: neg' =>
                        match cap with
                        | O => None
                        | S cap' =>
                            let kn := coeff_of a (c_ts n) in
                            (* [comment removed for export] *)
                            go neg' (cstr_comb (- kn) p kp n :: acc) cap'
                        end
                    end) neg acc cap in
      match res with
      | Some (acc', cap') => combine_all a pos' neg acc' cap'
      | None => None
      end
  end.

Fixpoint terms_atoms (ts : terms) : list expr :=
  match ts with [] => [] | (_, a) :: ts' => a :: terms_atoms ts' end.

Fixpoint fm_elim (ats : list expr) (cs : list cstr) (cap : nat) : option (list (N * Z)) :=
  match find_contra cs with
  | Some pv => Some pv
  | None =>
      match ats with
      | [] => None
      | a :: ats' =>
          let '(pos, neg, zer) := partition3 a cs [] [] [] in
          match combine_all a pos neg zer cap with
          | Some cs' => fm_elim ats' cs' cap
          | None => None
          end
      end
  end.

(* [comment removed for export] *)
Fixpoint cs_insert (c : cstr) (acc : list cstr) : list cstr :=
  match acc with
  | [] => [c]
  | d :: acc' => if terms_eqb (c_ts c) (c_ts d) then (if Z.leb (c_c d) (c_c c) then d :: acc' else c :: acc')
                 else d :: cs_insert c acc'
  end.

Fixpoint cs_dedup (cs : list cstr) (acc : list cstr) : list cstr :=
  match cs with [] => acc | c :: cs' => cs_dedup cs' (cs_insert c acc) end.

Fixpoint cs_atoms (cs : list cstr) (acc : list expr) : list expr :=
  match cs with [] => acc | c :: cs' => cs_atoms cs' (atoms_of_list (terms_atoms (c_ts c)) acc) end.

Fixpoint sign_counts (a : expr) (cs : list cstr) (p n : nat) : nat * nat :=
  match cs with
  | [] => (p, n)
  | c :: cs' => let k := coeff_of a (c_ts c) in
               if Z.ltb 0 k then sign_counts a cs' (S p) n
               else if Z.ltb k 0 then sign_counts a cs' p (S n) else sign_counts a cs' p n
  end.

Fixpoint best_atom (ats : list expr) (cs : list cstr) (best : option (expr * nat)) : option expr :=
  match ats with
  | [] => match best with Some (a, _) => Some a | None => None end
  | a :: ats' =>
      let '(p, n) := sign_counts a cs O O in
      let score := (p * n)%nat in
      match best with
      | Some (_, sb) => if Nat.ltb score sb then best_atom ats' cs (Some (a, score)) else best_atom ats' cs best
      | None => best_atom ats' cs (Some (a, score))
      end
  end.

(* [comment removed for export] *)
Definition fmst := (list (list (N * Z) * Z) * N)%type.

Fixpoint terms_gcd (ts : terms) (g : Z) : Z :=
  match ts with [] => g | (k, _) :: ts' => terms_gcd ts' (Z.gcd g k) end.

Definition cut_norm (c : cstr) (st : fmst) : cstr * fmst :=
  match c_ts c with
  | [] => (c, st)
  | _ => let g := terms_gcd (c_ts c) 0 in
         if Z.ltb 1 g && negb (Z.eqb (c_c c mod g) 0)
         then (CS (terms_divq g (c_ts c)) (c_c c / g) [(snd st, 1)], (fst st ++ [(c_pv c, g)], N.succ (snd st)))
         else (c, st)
  end.

Fixpoint cut_norm_all (cs : list cstr) (acc : list cstr) (st : fmst) : list cstr * fmst :=
  match cs with
  | [] => (rev acc, st)
  | c :: cs' => let '(c', st') := cut_norm c st in cut_norm_all cs' (c' :: acc) st'
  end.

(* [comment removed for export] *)
Fixpoint combine_allb (a : expr) (pos neg : list cstr) (acc : list cstr) (cap : nat) (st : fmst) : option (list cstr * nat * fmst) :=
  match pos with
  | [] => Some (acc, cap, st)
  | p :: pos' =>
      let kp := coeff_of a (c_ts p) in
      let res := (fix go (neg : list cstr) (acc : list cstr) (cap : nat) (st : fmst) : option (list cstr * nat * fmst) :=
                    match neg with
                    | [] => Some (acc, cap, st)
                    | n :: neg' =>
                        match cap with
                        | O => None
                        | S cap' =>
                            let kn := coeff_of a (c_ts n) in
                            let '(c', st') := cut_norm (cstr_comb (- kn) p kp n) st in
                            go neg' (c' :: acc) cap' st'
                        end
                    end) neg acc cap st in
      match res with
      | Some (acc', cap', st') => combine_allb a pos' neg acc' cap' st'
      | None => None
      end
  end.

Fixpoint fm_elim2 (fuel : nat) (cs : list cstr) (cap : nat) (st : fmst) : option cert :=
  match find_contra cs with
  | Some pv => Some (match fst st with [] => CFk pv | cuts => CFkX cuts pv end)
  | None =>
      match fuel with
      | O => None
      | S f =>
          let cs1 := cs_dedup cs [] in
          match best_atom (cs_atoms cs1 []) cs1 None with
          | None => None
          | Some a =>
              let '(pos, neg, zer) := partition3 a cs1 [] [] [] in
              match combine_allb a pos neg zer cap st with
              | Some (cs', cap', st') => fm_elim2 f cs' cap' st'
              | None => None
              end
          end
      end
  end.

Fixpoint cstrs_of (pool : list expr) (i : N) : list cstr :=
  match pool with
  | [] => []
  | e :: pool' => let '(ts, c) := lin_of e in CS ts c [(i, 1)] :: cstrs_of pool' (N.succ i)
  end.

(* [comment removed for export] *)
Fixpoint any_mem (xs : list expr) (ys : list expr) : bool :=
  match xs with [] => false | x :: xs' => expr_mem x ys || any_mem xs' ys end.

Fixpoint component (rounds : nat) (ats : list expr) (pending kept : list cstr) : list expr * list cstr :=
  match rounds with
  | O => (ats, kept)
  | S r =>
      let '(grab, rest) := partition (fun c => any_mem (terms_atoms (c_ts c)) ats) pending in
      match grab with
      | [] => (ats, kept)
      | _ => component r (atoms_of_list (map (fun c => of_terms (c_ts c) 0) grab) ats) rest (grab ++ kept)
      end
  end.

(* [comment removed for export] *)
Definition fm_cap : nat := 600%nat.

(* [comment removed for export] *)
Definition link_of (c : cstr) : option (expr * Z * bool) :=   (* [comment removed for export] *)
  if negb (Z.eqb (c_c c) 0) then None else
  match c_ts c with
  | [(k1, x1); (k2, x2)] =>
      let try1 (ka : Z) (a : expr) (kq : Z) (q : expr) :=
        match q with
        | EOp OShr y (ELit _) =>
            if expr_eqb y a then
              (if Z.eqb ka 1 && Z.ltb kq 0 then Some (a, - kq, true)
               else if Z.eqb ka (-1) && Z.ltb 0 kq then Some (a, kq, false) else None)
            else None
        | _ => None
        end in
      match try1 k1 x1 k2 x2 with Some r => Some r | None => try1 k2 x2 k1 x1 end
  | _ => None
  end.

Fixpoint find_link (cs : list cstr) (a : expr) (pol : bool) : option cstr :=
  match cs with
  | [] => None
  | c :: cs' => match link_of c with
               | Some (a', _, pol') => if expr_eqb a a' && Bool.eqb pol pol' then Some c else find_link cs' a pol
               | None => find_link cs' a pol
               end
  end.

Fixpoint subst_atom (a : expr) (lpos lneg : cstr) (cs : list cstr) (acc : list cstr) (st : fmst) : list cstr * fmst :=
  match cs with
  | [] => (rev acc, st)
  | c :: cs' =>
      match link_of c with
      | Some (a', _, _) => if expr_eqb a a' then subst_atom a lpos lneg cs' acc st      (* [comment removed for export] *)
                           else subst_atom a lpos lneg cs' (c :: acc) st
      | None =>
          let k := coeff_of a (c_ts c) in
          if Z.ltb 0 k then let '(c', st') := cut_norm (cstr_comb 1 c k lneg) st in subst_atom a lpos lneg cs' (c' :: acc) st'
          else if Z.ltb k 0 then let '(c', st') := cut_norm (cstr_comb 1 c (- k) lpos) st in subst_atom a lpos lneg cs' (c' :: acc) st'
          else subst_atom a lpos lneg cs' (c :: acc) st
      end
  end.

Fixpoint subst_links (fuel : nat) (cs : list cstr) (st : fmst) : list cstr * fmst :=
  match fuel with
  | O => (cs, st)
  | S f =>
      (* [comment removed for export] *)
      match (fix pick (l : list cstr) : option (expr * cstr * cstr) :=
               match l with
               | [] => None
               | c :: l' => match link_of c with
                            | Some (a, _, true) => match find_link cs a false with
                                                   | Some ln => Some (a, c, ln)
                                                   | None => pick l'
                                                   end
                            | _ => pick l'
                            end
               end) cs with
      | Some (a, lp, ln) => let '(cs', st') := subst_atom a lp ln cs [] st in subst_links f cs' st'
      | None => (cs, st)
      end
  end.

(* [comment removed for export] *)
Definition alias_of (c : cstr) : option (expr * expr * bool) :=   (* [comment removed for export] *)
  if negb (Z.eqb (c_c c) 0) then None else
  match c_ts c with
  | [(k1, x1); (k2, x2)] =>
      if Z.eqb k1 1 && Z.eqb k2 (-1) then Some (x1, x2, true)
      else if Z.eqb k1 (-1) && Z.eqb k2 1 then Some (x1, x2, false) else None
  | _ => None
  end.

Fixpoint find_alias (cs : list cstr) (a b : expr) (pol : bool) : option cstr :=
  match cs with
  | [] => None
  | c :: cs' => match alias_of c with
               | Some (a', b', pol') => if expr_eqb a a' && expr_eqb b b' && Bool.eqb pol pol' then Some c else find_alias cs' a b pol
               | None => find_alias cs' a b pol
               end
  end.

(* [comment removed for export] *)
Fixpoint subst_alias_atom (b : expr) (lpos lneg : cstr) (cs : list cstr) (acc : list cstr) (st : fmst) : list cstr * fmst :=
  match cs with
  | [] => (rev acc, st)
  | c :: cs' =>
      let k := coeff_of b (c_ts c) in
      if Z.ltb 0 k then let '(c', st') := cut_norm (cstr_comb 1 c k lneg) st in subst_alias_atom b lpos lneg cs' (c' :: acc) st'
      else if Z.ltb k 0 then let '(c', st') := cut_norm (cstr_comb 1 c (- k) lpos) st in subst_alias_atom b lpos lneg cs' (c' :: acc) st'
      else subst_alias_atom b lpos lneg cs' (c :: acc) st
  end.

Fixpoint subst_aliases (fuel : nat) (cs : list cstr) (st : fmst) : list cstr * fmst :=
  match fuel with
  | O => (cs, st)
  | S f =>
      match (fix pick (l : list cstr) : option (expr * cstr * cstr) :=
               match l with
               | [] => None
               | c :: l' => match alias_of c with
                            | Some (a, b, true) => match find_alias cs a b false with
                                                   | Some cn => Some (b, cn, c)     (* [comment removed for export] *)
                                                   | None => pick l'
                                                   end
                            | _ => pick l'
                            end
               end) cs with
      | Some (b, lp, ln) => let '(cs', st') := subst_alias_atom b lp ln cs [] st in subst_aliases f cs' st'
      | None => (cs, st)
      end
  end.

(* [comment removed for export] *)
Definition fm_search_gen (deep : bool) (ngoals : nat) (pool : list expr) : option cert :=
  let '(csn, stn) := cut_norm_all (cstrs_of pool 0%N) [] ([], N.of_nat (length pool)) in
  let '(csa, sta) := subst_aliases 64%nat csn stn in
  let '(cs0, st0) := subst_links 16%nat csa sta in
  let gs := firstn ngoals cs0 in let rest := skipn ngoals cs0 in
  (* [comment removed for export] *)
  let lits := filter (fun c => match c_ts c with [] => true | _ => false end) rest in
  let ga := atoms_of_list (map (fun c => of_terms (c_ts c) 0) gs) [] in
  (* [comment removed for export] *)
  let '(ats1, cs1) := component 1%nat ga rest gs in
  match fm_elim2 (S (length ats1)) (cs1 ++ lits) fm_cap st0 with
  | Some c => Some c
  | None =>
  let '(ats2, cs2) := component 2%nat ga rest gs in
  match (if Nat.eqb (length cs2) (length cs1) then None else fm_elim2 (S (length ats2)) (cs2 ++ lits) fm_cap st0) with
  | Some c => Some c
  | None =>
      if deep then
        let '(ats, cs) := component 12%nat ga rest gs in
        if Nat.eqb (length cs) (length cs2) then None
        else fm_elim2 (S (length ats)) (cs ++ lits) fm_cap st0
      else None
  end
  end.
Definition fm_search : nat -> list expr -> option cert := fm_search_gen true.
(* [comment removed for export] *)
Definition fm_search0 : nat -> list expr -> option cert := fm_search_gen false.

(* [comment removed for export] *)
Fixpoint pf_index_sep (pf : list pfact) (i : N) (acc : list (N * pfact)) : list (N * pfact) :=
  match pf with
  | [] => acc
  | (FSep _ _ _ _ as f) :: pf' | (FSep0 _ _ _ _ _ as f) :: pf' => pf_index_sep pf' (N.succ i) ((i, f) :: acc)
  | _ :: pf' => pf_index_sep pf' (N.succ i) acc
  end.

Fixpoint search_splits (skipfm : bool) (ng : nat) (depth : nat) (seps : list (N * pfact)) (pool : list expr) : option cert :=
  match (if skipfm then None else fm_search ng pool) with
  | Some c => Some c
  | None =>
      match depth with
      | O => None
      | S d =>
          (fix try_each (l : list (N * pfact)) : option cert :=
             match l with
             | [] => None
             | (j, FSep a n b k) :: l' =>
                 match search_splits false (S ng) d l' (sep_l a n b :: pool) with
                 | Some cl =>
                     match search_splits false (S ng) d l' (sep_r a b k :: pool) with
                     | Some cr => Some (CSp j cl cr)
                     | None => try_each l'
                     end
                 | None => try_each l'
                 end
             | (j, FSep0 z a n b k) :: l' =>
                 match search_splits false (S (S ng)) d l' (z :: emulc (-1) z :: pool) with
                 | Some c0 =>
                   match search_splits false (S ng) d l' (sep_l a n b :: pool) with
                   | Some cl =>
                       match search_splits false (S ng) d l' (sep_r a b k :: pool) with
                       | Some cr => Some (CSp0 j c0 cl cr)
                       | None => try_each l'
                       end
                   | None => try_each l'
                   end
                 | None => try_each l'
                 end
             | _ :: l' => try_each l'
             end) seps
      end
  end.

(* [comment removed for export] *)
Definition sep_forms (f : pfact) : list expr :=
  match f with
  | FSep a n b k => [sep_l a n b; sep_r a b k]
  | FSep0 z a n b k => [z; sep_l a n b; sep_r a b k]
  | _ => []
  end.

(* [comment removed for export] *)
Definition side_rel (ga : list expr) (l : list expr) : bool :=
  match atoms_of_list l [] with
  | [] => true
  | ats => any_mem ats ga
  end.

Definition sep_rel (ga : list expr) (f : pfact) : bool :=
  match f with
  | FSep a n b k => side_rel ga [a; n] && side_rel ga [b; k]
  | FSep0 z a n b k => side_rel ga [a; n] && side_rel ga [b; k]
  | _ => false
  end.

(* [comment removed for export] *)
Definition pf_exprs (f : pfact) : list expr :=
  match f with
  | FGe e => [e]
  | FSep a n b k => [a; n; b; k]
  | FSep0 z a n b k => [z; a; n; b; k]
  | FAl a _ => [a]
  | FCr a n => [a; n]
  | FShb _ c oa on => [c; oa; on]
  | FLe a b | FLt a b | FEq a b => [a; b]
  | FOr2 a b c d => [a; b; c; d]
  | FOr3z z a b c d => [z; a; b; c; d]
  | FProp _ args => args
  end.
Definition hyp_score (ga : list expr) (h : pfact) : nat :=
  length (filter (fun a => expr_mem a ga) (atoms_of_list (pf_exprs h) [])).
Fixpoint ins_rankedN (sc : nat) (jf : N * pfact) (l : list (nat * (N * pfact))) : list (nat * (N * pfact)) :=
  match l with
  | [] => [(sc, jf)]
  | (sc', jf') :: l' => if Nat.ltb sc' sc then (sc, jf) :: l else (sc', jf') :: ins_rankedN sc jf l'
  end.
Fixpoint rank_seps (ga : list expr) (l : list (N * pfact)) (acc : list (nat * (N * pfact))) : list (N * pfact) :=
  match l with
  | [] => map snd acc
  | jf :: l' => rank_seps ga l' (ins_rankedN (hyp_score ga (snd jf)) jf acc)
  end.

Definition relevant_seps (pf : list pfact) (goals : list expr) : list (N * pfact) :=
  let ga := atoms_of_list goals [] in
  rank_seps ga (filter (fun jf => sep_rel ga (snd jf)) (pf_index_sep pf 0%N [])) [].

Definition relevant_sepsX (pf : list pfact) (goals : list expr) (pool : list expr) : list (N * pfact) :=
  let seps := pf_index_sep pf 0%N [] in
  let pseudo := cstrs_of (flat_map (fun jf => sep_forms (snd jf)) seps ++ pool) 0%N in
  let ga := atoms_of_list goals [] in
  let '(ca, _) := component 12%nat ga pseudo [] in
  rank_seps ga (filter (fun jf => sep_rel ca (snd jf)) seps) [].

Definition split_depth : nat := 2%nat.

Fixpoint all_lits_false (goals : list expr) : option bool :=
  match goals with
  | [] => Some false
  | g :: gs => match is_lit g with
               | Some c => if Z.leb 0 c then Some true else all_lits_false gs
               | None => None
               end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hK : int := 1099511628211%uint63.
Definition hmix (h x : int) : int :=
  let y := PrimInt63.mul (PrimInt63.lxor h x) hK in PrimInt63.lxor y (PrimInt63.lsr y 29%uint63).
(* [comment removed for export] *)
Fixpoint hposb (p : positive) (acc nb h : int) : int :=
  match p with
  | xH => hmix (hmix h (PrimInt63.lor acc (PrimInt63.lsl 1%uint63 nb))) (PrimInt63.add nb 1%uint63)
  | xO q => if PrimInt63.eqb nb 61%uint63 then hposb q 0%uint63 0%uint63 (hmix h acc)
            else hposb q acc (PrimInt63.add nb 1%uint63) h
  | xI q => if PrimInt63.eqb nb 61%uint63 then hposb q 0%uint63 0%uint63 (hmix h (PrimInt63.lor acc (PrimInt63.lsl 1%uint63 nb)))
            else hposb q (PrimInt63.lor acc (PrimInt63.lsl 1%uint63 nb)) (PrimInt63.add nb 1%uint63) h
  end.
Definition hpos (p : positive) (h : int) : int := hposb p 0%uint63 0%uint63 h.
Fixpoint i63_of_pos (p : positive) : int :=
  match p with
  | xH => 1%uint63
  | xO q => PrimInt63.lsl (i63_of_pos q) 1%uint63
  | xI q => PrimInt63.lor (PrimInt63.lsl (i63_of_pos q) 1%uint63) 1%uint63
  end.
Definition i63_of_Z (z : Z) : int :=
  match z with Z0 => 0%uint63 | Zpos p => i63_of_pos p | Zneg p => PrimInt63.sub 0%uint63 (i63_of_pos p) end.
Definition hZ (z : Z) (h : int) : int :=
  match z with
  | Z0 => hmix h 7%uint63
  | Zpos p => hpos p (hmix h 11%uint63)
  | Zneg p => hpos p (hmix h 13%uint63)
  end.
Fixpoint hexpr (e : expr) (h : int) : int :=
  match e with
  | ELit z => hZ z (hmix h 17%uint63)
  | EZv i => hpos i (hmix h 19%uint63)
  | EUv i => hpos i (hmix h 23%uint63)
  | EAdd a b => hexpr b (hexpr a (hmix h 29%uint63))
  | EMulC c a => hexpr a (hZ c (hmix h 31%uint63))
  | EOp o a b => hexpr b (hexpr a (hZ (opk_idx o) (hmix h 37%uint63)))
  end.
Fixpoint hexprs (l : list expr) (h : int) : int :=
  match l with [] => hmix h 41%uint63 | e :: l' => hexprs l' (hexpr e (hmix h 43%uint63)) end.
Definition hpfact (f : pfact) (h : int) : int :=
  match f with
  | FGe e => hexpr e (hmix h 47%uint63)
  | FSep a n b k => hexprs [a; n; b; k] (hmix h 53%uint63)
  | FSep0 z a n b k => hexprs [z; a; n; b; k] (hmix h 59%uint63)
  | FAl a k => hexpr a (hZ (Z.of_N k) (hmix h 61%uint63))
  | FCr a n => hexprs [a; n] (hmix h 67%uint63)
  | FShb k c oa on => hexprs [c; oa; on] (hpos k (hmix h 71%uint63))
  | FLe a b => hexprs [a; b] (hmix h 73%uint63)
  | FLt a b => hexprs [a; b] (hmix h 79%uint63)
  | FEq a b => hexprs [a; b] (hmix h 83%uint63)
  | FOr2 a b c d => hexprs [a; b; c; d] (hmix h 89%uint63)
  | FOr3z z a b c d => hexprs [z; a; b; c; d] (hmix h 97%uint63)
  | FProp j args => hexprs args (hZ (Z.of_nat j) (hmix h 101%uint63))
  end.
Fixpoint hpf (pf : list pfact) (h : int) : int :=
  match pf with [] => hmix h 103%uint63 | f :: pf' => hpf pf' (hpfact f (hmix h 107%uint63)) end.
(* [comment removed for export] *)
Definition qhash (kind : int) (pf : list pfact) (goals : list expr) : int :=
  let h := hpf pf (hexprs goals (hmix 5472609002491716901%uint63 kind)) in
  PrimInt63.land (PrimInt63.lxor h (PrimInt63.lsr h 31%uint63)) 4611686018427387903%uint63.

Class lx_hints : Set := LXH { lxh_pos : list (int * cert); lxh_neg : list int }.
Definition lxh_empty : lx_hints := LXH [] [].

Fixpoint hfind (h : int) (l : list (int * cert)) : option cert :=
  match l with
  | [] => None
  | (k, c) :: l' => if PrimInt63.eqb h k then Some c else hfind h l'
  end.
Fixpoint hmem (h : int) (l : list int) : bool :=
  match l with [] => false | k :: l' => if PrimInt63.eqb h k then true else hmem h l' end.

(* [comment removed for export] *)
Fixpoint zdec_pv (n : nat) (l : list Z) (acc : list (N * Z)) : list (N * Z) * list Z :=
  match n with
  | O => (rev acc, l)
  | S n' => match l with i :: x :: l' => zdec_pv n' l' ((Z.to_N i, x) :: acc) | _ => (rev acc, []) end
  end.
Fixpoint zdec_cuts (n : nat) (l : list Z) (acc : list (list (N * Z) * Z)) : list (list (N * Z) * Z) * list Z :=
  match n with
  | O => (rev acc, l)
  | S n' => match l with
            | g :: k :: l' => let '(pv, l'') := zdec_pv (Z.to_nat k) l' [] in zdec_cuts n' l'' ((pv, g) :: acc)
            | _ => (rev acc, [])
            end
  end.
Fixpoint zdec_cert (fuel : nat) (l : list Z) : cert * list Z :=
  match fuel with
  | O => (CFk [], [])
  | S f =>
      match l with
      | 0 :: k :: l' => let '(pv, r) := zdec_pv (Z.to_nat k) l' [] in (CFk pv, r)
      | 1 :: k :: l' => let '(cuts, r) := zdec_cuts (Z.to_nat k) l' [] in
                        match r with
                        | k2 :: r' => let '(pv, r'') := zdec_pv (Z.to_nat k2) r' [] in (CFkX cuts pv, r'')
                        | [] => (CFk [], [])
                        end
      | 2 :: j :: l' => let '(cl, r) := zdec_cert f l' in let '(cr, r') := zdec_cert f r in (CSp (Z.to_N j) cl cr, r')
      | 3 :: j :: l' => let '(c0, r) := zdec_cert f l' in let '(cl, r') := zdec_cert f r in let '(cr, r'') := zdec_cert f r' in
                        (CSp0 (Z.to_N j) c0 cl cr, r'')
      | _ => (CFk [], [])
      end
  end.
Definition lxh_of_Z (pos : list (Z * list Z)) (neg : list Z) : lx_hints :=
  LXH (map (fun p => (i63_of_Z (fst p), fst (zdec_cert 32%nat (snd p)))) pos) (map i63_of_Z neg).

(* [comment removed for export] *)
Fixpoint nat_of_i63 (bits : nat) (x : int) : nat :=
  match bits with
  | O => O
  | S b => let r := nat_of_i63 b (PrimInt63.lsr x 1%uint63) in
           if PrimInt63.eqb (PrimInt63.land x 1%uint63) 1%uint63 then S (r + r) else (r + r)%nat
  end.
(* [comment removed for export] *)
Record lxps := LXPS { ps_num : Z; ps_neg : bool; ps_has : bool; ps_tag : int; ps_h : int; ps_hx : nat;
                      ps_nums : list Z; ps_pos : list (int * list Z); ps_negs : list int }.
Definition ps_endnum (st : lxps) : lxps :=
  if ps_has st then LXPS 0 false false (ps_tag st) (ps_h st) (ps_hx st) ((if ps_neg st then Z.opp (ps_num st) else ps_num st) :: ps_nums st) (ps_pos st) (ps_negs st)
  else st.
Definition ps_endentry (st : lxps) : lxps :=
  let st := ps_endnum st in
  if PrimInt63.eqb (ps_tag st) 1%uint63 then LXPS 0 false false 0%uint63 0%uint63 O [] ((ps_h st, rev (ps_nums st)) :: ps_pos st) (ps_negs st)
  else if PrimInt63.eqb (ps_tag st) 2%uint63 then LXPS 0 false false 0%uint63 0%uint63 O [] (ps_pos st) (ps_h st :: ps_negs st)
  else LXPS 0 false false 0%uint63 0%uint63 O [] (ps_pos st) (ps_negs st).
Definition ps_char (c : int) (st : lxps) : lxps :=
  if PrimInt63.eqb c 80%uint63 (* [comment removed for export] *) then let st := ps_endentry st in LXPS 0 false false 1%uint63 0%uint63 16%nat [] (ps_pos st) (ps_negs st)
  else if PrimInt63.eqb c 78%uint63 (* [comment removed for export] *) then let st := ps_endentry st in LXPS 0 false false 2%uint63 0%uint63 16%nat [] (ps_pos st) (ps_negs st)
  else match ps_hx st with
  | S hx => (* [comment removed for export] *)
      let d := if PrimInt63.ltb c 58%uint63 then PrimInt63.sub c 48%uint63 else PrimInt63.sub c 87%uint63 in
      LXPS 0 false false (ps_tag st) (PrimInt63.lor (PrimInt63.lsl (ps_h st) 4%uint63) d) hx (ps_nums st) (ps_pos st) (ps_negs st)
  | O =>
      if PrimInt63.eqb c 32%uint63 (* [comment removed for export] *) then ps_endnum st
      else if PrimInt63.eqb c 45%uint63 (* [comment removed for export] *) then LXPS 0 true true (ps_tag st) (ps_h st) O (ps_nums st) (ps_pos st) (ps_negs st)
      else (* [comment removed for export] *)
        let d := PrimInt63.sub c 48%uint63 in
        let dz := (if PrimInt63.eqb d 0%uint63 then 0 else if PrimInt63.eqb d 1%uint63 then 1 else if PrimInt63.eqb d 2%uint63 then 2
                   else if PrimInt63.eqb d 3%uint63 then 3 else if PrimInt63.eqb d 4%uint63 then 4 else if PrimInt63.eqb d 5%uint63 then 5
                   else if PrimInt63.eqb d 6%uint63 then 6 else if PrimInt63.eqb d 7%uint63 then 7 else if PrimInt63.eqb d 8%uint63 then 8 else 9)%Z in
        LXPS (Z.add (Z.mul 10 (ps_num st)) dz)
             (ps_neg st) true (ps_tag st) (ps_h st) O (ps_nums st) (ps_pos st) (ps_negs st)
  end.
Fixpoint ps_scan (fuel : nat) (s : PrimString.string) (i : int) (st : lxps) : lxps :=
  match fuel with
  | O => st
  | S f => ps_scan f s (PrimInt63.add i 1%uint63) (ps_char (PrimString.get s i) st)
  end.
Definition lxh_parse (s : PrimString.string) : lx_hints :=
  let n := PrimString.length s in
  let st := ps_endentry (ps_scan (nat_of_i63 25%nat n) s 0%uint63 (LXPS 0 false false 0%uint63 0%uint63 O [] [] [])) in
  LXH (map (fun p => (fst p, fst (zdec_cert 32%nat (snd p)))) (ps_pos st)) (ps_negs st).
(* [comment removed for export] *)
Definition lxh_ids (s : PrimString.string) : PrimString.string := s.
Module LxhSyntax.
  Declare Scope lxh_scope.
  Delimit Scope lxh_scope with lxh.
  String Notation PrimString.string lxh_ids lxh_ids : lxh_scope.
End LxhSyntax.

(* [comment removed for export] *)
Definition lx_note (h : int) (npool : N) (r : option cert) : option cert := r.

Definition chk_cert (pf : list pfact) (pool : list expr) (r : option cert) : bool :=
  match r with Some c => cert_check pf pool c | None => false end.

Section Hinted.
  Context {lxHT : lx_hints}.

  (* [comment removed for export] *)
  Definition lx_decide (kind : int) (pf : list pfact) (goals : list expr) (pool : list expr)
             (srch : unit -> option cert) : bool :=
    let h := qhash kind pf goals in
    match hfind h (@lxh_pos lxHT) with
    | Some c => if cert_check pf pool c then true else chk_cert pf pool (srch tt)
    | None => if hmem h (@lxh_neg lxHT) then false else chk_cert pf pool (lx_note h (N.of_nat (length pool)) (srch tt))
    end.

  Lemma lx_decide_true : forall kind pf goals pool srch,
    lx_decide kind pf goals pool srch = true -> exists c, cert_check pf pool c = true.
  Proof.
    intros kind pf goals pool srch H. unfold lx_decide, chk_cert, lx_note in H.
    destruct (hfind _ _) as [c|].
    - destruct (cert_check pf pool c) eqn:E; [exists c; exact E|].
      destruct (srch tt) as [c'|]; [exists c'; exact H|discriminate].
    - destruct (hmem _ _); [discriminate|].
      destruct (srch tt) as [c'|]; [exists c'; exact H|discriminate].
  Qed.

(* [comment removed for export] *)
Definition lin_ge_gen (ext : bool) (pf : list pfact) (goals : list expr) : bool :=
  match all_lits_false goals with
  | Some b => b
  | None =>
      let pool := base_pool pf goals in
      lx_decide (if ext then 2 else 1)%uint63 pf goals pool (fun _ =>
        match fm_search (length goals) pool with
        | Some c => Some c
        | None =>
            search_splits true (length goals) split_depth
              (if ext then relevant_sepsX pf goals pool else relevant_seps pf goals) pool
        end)
  end.

Definition lin_ge_list (pf : list pfact) (goals : list expr) : bool := lin_ge_gen false pf goals.

(* [comment removed for export] *)
Definition lin_ge_splits (ext : bool) (pf : list pfact) (goals : list expr) : bool :=
  match all_lits_false goals with
  | Some b => b
  | None =>
      let pool := base_pool pf goals in
      lx_decide (if ext then 4 else 3)%uint63 pf goals pool (fun _ =>
        search_splits true (length goals) split_depth
          (if ext then relevant_sepsX pf goals pool else relevant_seps pf goals) pool)
  end.
Definition lin_geS (pf : list pfact) (goal : expr) : bool := lin_ge_splits false pf [goal].

(* [comment removed for export] *)
Definition lin_ge0 (pf : list pfact) (goal : expr) : bool :=
  match all_lits_false [goal] with
  | Some b => b
  | None =>
      let pool := base_pool pf [goal] in
      lx_decide 5%uint63 pf [goal] pool (fun _ => fm_search 1%nat pool)
  end.

(* [comment removed for export] *)
Definition lin_ge_fm (deep : bool) (pf : list pfact) (goals : list expr) : bool :=
  match all_lits_false goals with
  | Some b => b
  | None =>
      let pool := base_pool pf goals in
      lx_decide (if deep then 7 else 6)%uint63 pf goals pool (fun _ => fm_search_gen deep (length goals) pool)
  end.

(* [comment removed for export] *)
Definition lin_ge00 (pf : list pfact) (goal : expr) : bool :=
  match all_lits_false [goal] with
  | Some b => b
  | None =>
      let pool := base_pool pf [goal] in
      lx_decide 8%uint63 pf [goal] pool (fun _ => fm_search0 1%nat pool)
  end.

(* [comment removed for export] *)
Definition refute (pf : list pfact) (e : expr) : bool := lin_ge0 pf (eadd (emulc (-1) e) (ELit (-1))).

(* [comment removed for export] *)
Definition settle1 (pf : list pfact) (f : pfact) : pfact :=
  match f with
  | FSep a n b k =>
      if refute pf (sep_l a n b) then FGe (sep_r a b k)
      else if refute pf (sep_r a b k) then FGe (sep_l a n b) else f
  | FSep0 z a n b k =>
      if (if lin_ge0 pf (eadd z (ELit (-1))) then true else lin_ge0 pf (eadd (emulc (-1) z) (ELit (-1)))) then
        (if refute pf (sep_l a n b) then FGe (sep_r a b k)
         else if refute pf (sep_r a b k) then FGe (sep_l a n b) else FSep a n b k)
      else f
  | _ => f
  end.

Definition settle_seps (pf : list pfact) : list pfact := map (settle1 pf) pf.
Definition lin_ge_listX (pf : list pfact) (goals : list expr) : bool := lin_ge_gen true pf goals.

Definition lin_ge (pf : list pfact) (goal : expr) : bool := lin_ge_list pf [goal].
Definition lin_geX (pf : list pfact) (goal : expr) : bool := lin_ge_listX pf [goal].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition pf_knows (pf : list pfact) (a : expr) : bool :=
  expr_mem a (atoms_of_list (flat_map pf_exprs pf) []).

Definition mk_oracle (pf : list pfact) : oracle :=
  ORA (lin_ge pf) (al_lookup pf) (pf_knows pf).

(* [comment removed for export] *)
Definition dec_le (pf : list pfact) (a b : expr) : bool := lin_ge pf (eadd b (emulc (-1) a)).        (* [comment removed for export] *)
Definition dec_lt (pf : list pfact) (a b : expr) : bool := lin_ge pf (eadd b (eadd (emulc (-1) a) (ELit (-1)))). (* [comment removed for export] *)
Definition dec_eq (pf : list pfact) (a b : expr) : bool := if dec_le pf a b then dec_le pf b a else false.

(* [comment removed for export] *)
Definition dec_leX (pf : list pfact) (a b : expr) : bool := lin_geX pf (eadd b (emulc (-1) a)).       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition dec_le0 (pf : list pfact) (a b : expr) : bool := lin_ge0 pf (eadd b (emulc (-1) a)).        (* [comment removed for export] *)
Definition dec_le00 (pf : list pfact) (a b : expr) : bool := lin_ge00 pf (eadd b (emulc (-1) a)).      (* [comment removed for export] *)
Definition dec_inside0 (pf : list pfact) (a n b k : expr) : bool :=
  if dec_le0 pf b a then dec_le0 pf (eadd a n) (eadd b k) else false.
Definition dec_inside1 (pf : list pfact) (a n b k : expr) : bool :=
  if dec_le pf b a then dec_le pf (eadd a n) (eadd b k) else false.
Definition dec_insideX (pf : list pfact) (a n b k : expr) : bool :=
  if dec_leX pf b a then dec_leX pf (eadd a n) (eadd b k) else false.
Definition dec_inside (pf : list pfact) (a n b k : expr) : bool :=
  if dec_inside1 pf a n b k then true else dec_insideX pf a n b k.

(* [comment removed for export] *)
Fixpoint any_iv (test : expr -> expr -> bool) (ivs : list (expr * expr)) : bool :=
  match ivs with
  | [] => false
  | (b, k) :: ivs' => if test b k then true else any_iv test ivs'
  end.

(* [comment removed for export] *)
Definition iv_inside_syn (x m A N : expr) : bool :=
  match ediff_lit x A with
  | Some d => Z.leb 0 d && match is_lit m, is_lit N with
                          | Some mz, Some nz => Z.leb (d + mz) nz
                          | _, _ => Z.eqb d 0 && expr_eqb m N
                          end
  | None => false
  end.

Definition sep_sides (a n b k A N B K : expr) : bool :=
  (iv_inside_syn a n A N && iv_inside_syn b k B K) || (iv_inside_syn a n B K && iv_inside_syn b k A N).

(* [comment removed for export] *)
Fixpoint sep_lookup (zok : bool) (pf : list pfact) (a n b k : expr) : bool :=
  match pf with
  | [] => false
  | FSep A N B K :: pf' => sep_sides a n b k A N B K || sep_lookup zok pf' a n b k
  | FSep0 z A N B K :: pf' =>
      (zok && (expr_eqb z n || expr_eqb z k) && sep_sides a n b k A N B K) || sep_lookup zok pf' a n b k
  | _ :: pf' => sep_lookup zok pf' a n b k
  end.

(* [comment removed for export] *)
Definition dec_apart (pf : list pfact) (a n b k : expr) : bool :=
  if sep_lookup false pf a n b k then true else
  if lin_ge_list pf [sep_l a n b; sep_r a b k] then true else lin_ge_listX pf [sep_l a n b; sep_r a b k].

End Hinted.
