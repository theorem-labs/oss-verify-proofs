(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.

Definition terms := list (nat * Z).
Definition lin : Type := (Z * terms)%type.

Definition valuation := nat -> Z.

Fixpoint teval (ρ : valuation) (ts : terms) : Z :=
  match ts with
  | [] => 0
  | (x, a) :: r => a * ρ x + teval ρ r
  end.

Definition leval (ρ : valuation) (f : lin) : Z := fst f + teval ρ (snd f).

Definition lconst (c : Z) : lin := (c, []).
Definition lvar (x : nat) : lin := (0, [(x, 1)]).

Fixpoint tadd (a : terms) : terms -> terms :=
  match a with
  | [] => fun b => b
  | (x, p) :: ra =>
      fix tadd_b (b : terms) : terms :=
        match b with
        | [] => a
        | (y, q) :: rb =>
            if Nat.ltb x y then (x, p) :: tadd ra b
            else if Nat.ltb y x then (y, q) :: tadd_b rb
            else let s := p + q in if s =? 0 then tadd ra rb else (x, s) :: tadd ra rb
        end
  end.

Definition tscale (k : Z) (ts : terms) : terms := map (fun p => (fst p, k * snd p)) ts.

Definition ladd (f g : lin) : lin := (fst f + fst g, tadd (snd f) (snd g)).
Definition lscale (k : Z) (f : lin) : lin :=
  if k =? 0 then (0, []) else (k * fst f, tscale k (snd f)).
Definition laddc (f : lin) (c : Z) : lin := (fst f + c, snd f).
Definition lsub (f g : lin) : lin := ladd f (lscale (-1) g).

Fixpoint teqb (a b : terms) : bool :=
  match a, b with
  | [], [] => true
  | (x, p) :: ra, (y, q) :: rb => Nat.eqb x y && (p =? q) && teqb ra rb
  | _, _ => false
  end.

Definition tmult (k : Z) (g f : terms) : bool := teqb g (tscale k f).

Definition tratio (g f : terms) : option Z :=
  match g, f with
  | (x, p) :: _, (y, q) :: _ => if negb (Nat.eqb x y) then None else if (q =? 0) then None else if (p mod q =? 0) then
                                  (let k := p / q in if tmult k g f then Some k else None) else None
  | _, _ => None
  end.

Record fact : Type := Fact { fc_f : lin; fc_lo : Z; fc_hi : Z }.

Definition fact_sat (ρ : valuation) (x : fact) : Prop := fc_lo x <= leval ρ (fc_f x) <= fc_hi x.

Definition store := list fact.

Definition sat (ρ : valuation) (s : store) : Prop := Forall (fact_sat ρ) s.

Definition ivl : Type := (Z * Z)%type.

Definition imeet (a b : option ivl) : option ivl :=
  match a, b with
  | None, x => x
  | x, None => x
  | Some (l1, h1), Some (l2, h2) => Some (Z.max l1 l2, Z.min h1 h2)
  end.

Fixpoint vbound (s : store) (x : nat) : option ivl :=
  match s with
  | [] => None
  | Fact (c, [(y, a)]) lo hi :: r =>
      if (a =? 1) && Nat.eqb x y then Some (lo - c, hi - c) else vbound r x
  | _ :: r => vbound r x
  end.

Definition iscale (a : Z) (i : ivl) : ivl :=
  if 0 <=? a then (a * fst i, a * snd i) else (a * snd i, a * fst i).

Fixpoint tbox (s : store) (ts : terms) : option ivl :=
  match ts with
  | [] => Some (0, 0)
  | (x, a) :: r =>
      match vbound s x, tbox s r with
      | Some i, Some j => let k := iscale a i in Some (fst k + fst j, snd k + snd j)
      | _, _ => None
      end
  end.

Fixpoint trel (s : store) (c : Z) (ts : terms) : option ivl :=
  match s with
  | [] => None
  | Fact f lo hi :: r =>
      let rest := trel r c ts in
      match tratio ts (snd f) with
      | Some k =>

          let i := iscale k (lo - fst f, hi - fst f) in imeet (Some (c + fst i, c + snd i)) rest
      | None => rest
      end
  end.

Definition lrange0 (s : store) (g : lin) : option ivl :=
  match snd g with
  | [] => Some (fst g, fst g)
  | ts => imeet (match tbox s ts with Some i => Some (fst g + fst i, fst g + snd i) | None => None end)
                (trel s (fst g) ts)
  end.

Fixpoint tcoef (ts : terms) (x : nat) : Z :=
  match ts with
  | [] => 0
  | (y, a) :: r => if Nat.eqb x y then a else tcoef r x
  end.

Definition cdiv (a b : Z) : Z := - ((- a) / b).

Definition elim1 (s : store) (g : lin) (fc : fact) : option ivl :=
  match snd g with
  | (x, gx) :: _ =>
      let fx := tcoef (snd (fc_f fc)) x in
      if fx =? 0 then None else
      let r := lsub (lscale fx g) (lscale gx (fc_f fc)) in
      match tbox s (snd r) with
      | Some (rl, rh) =>
          let i := iscale gx (fc_lo fc, fc_hi fc) in
          let lo' := fst i + fst r + rl in
          let hi' := snd i + fst r + rh in
          if 0 <? fx then Some (cdiv lo' fx, hi' / fx) else Some (cdiv (- hi') (- fx), (- lo') / (- fx))
      | None => None
      end
  | [] => None
  end.

Definition relational (fc : fact) : bool := match snd (fc_f fc) with _ :: _ :: _ => true | _ => false end.

Fixpoint trel2 (s0 s : store) (g : lin) : option ivl :=
  match s with
  | [] => None
  | fc :: r => if relational fc then imeet (elim1 s0 g fc) (trel2 s0 r g) else trel2 s0 r g
  end.

Definition lrange (s : store) (g : lin) : option ivl :=
  match snd g with
  | [] => Some (fst g, fst g)
  | _ => imeet (lrange0 s g) (trel2 s s g)
  end.

Fixpoint sadd_m (s : store) (ts : terms) (lo hi : Z) : option store :=
  match s with
  | [] => None
  | Fact (c, ts') lo' hi' :: r =>
      if teqb ts ts' then Some (Fact (0, ts) (Z.max lo (lo' - c)) (Z.min hi (hi' - c)) :: r)
      else match sadd_m r ts lo hi with
           | Some r' => Some (Fact (c, ts') lo' hi' :: r')
           | None => None
           end
  end.

Definition sadd0 (s : store) (f : lin) (lo hi : Z) : store :=
  match snd f with
  | [] => s
  | _ => match sadd_m s (snd f) (lo - fst f) (hi - fst f) with
         | Some s' => s'
         | None => Fact f lo hi :: s
         end
  end.

Definition tremove (ts : terms) (x : nat) : terms := filter (fun p => negb (Nat.eqb (fst p) x)) ts.
Definition tcoefs (ts : terms) (x : nat) : Z := fold_right (fun p acc => if Nat.eqb (fst p) x then snd p + acc else acc) 0 ts.

Definition xbound (s : store) (f : lin) (lo hi : Z) (x : nat) : option ivl :=
  let a := tcoefs (snd f) x in
  match tbox s (tremove (snd f) x) with
  | Some (ol, oh) =>
      let l' := lo - fst f - oh in let h' := hi - fst f - ol in
      if 0 <? a then Some (cdiv l' a, h' / a)
      else if a <? 0 then Some (cdiv (- h') (- a), (- l') / (- a)) else None
  | None => None
  end.

Fixpoint sprop (s : store) (f : lin) (lo hi : Z) (ts : terms) : store :=
  match ts with
  | [] => s
  | (x, _) :: r =>
      let s' := match xbound s f lo hi x with Some (xl, xh) => sadd0 s (lvar x) xl xh | None => s end in
      sprop s' f lo hi r
  end.

Definition sadd (s : store) (f : lin) (lo hi : Z) : store := sprop (sadd0 s f lo hi) f lo hi (snd f).

Fixpoint pick1 (ts : terms) : option (nat * Z) :=
  match ts with
  | [] => None
  | (x, a) :: r => match pick1 r with Some p => Some p | None => if (a =? 1) || (a =? -1) then Some (x, a) else None end
  end.

Definition subst1 (f : lin) (fc : fact) : lin :=
  if fc_lo fc =? fc_hi fc then
    match pick1 (snd (fc_f fc)) with
    | Some (x, a) =>
        let k := tcoefs (snd f) x in
        if k =? 0 then f else lsub f (lscale (k * a) (laddc (fc_f fc) (- fc_lo fc)))
    | None => f
    end
  else f.

Definition lnorm (s : store) (f : lin) : lin := fold_left subst1 s f.

