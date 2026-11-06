(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith PArith NArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive opk : Set := OAnd | OOr | OXor | OShr | OMul | OLow | OSx | OLtu | OLts | ODivU | ORemU
  | OShl.   (* [comment removed for export] *)

Inductive expr : Set :=
| ELit (z : Z)
| EZv (i : positive)            (* [comment removed for export] *)
| EUv (i : positive)            (* [comment removed for export] *)
| EAdd (a b : expr)
| EMulC (c : Z) (a : expr)
| EOp (o : opk) (a b : expr).

(* [comment removed for export] *)
Inductive sreg : Set := RW (i : positive) | RZ (e : expr).

Definition opk_eqb (a b : opk) : bool :=
  match a, b with
  | OAnd, OAnd | OOr, OOr | OXor, OXor | OShr, OShr | OMul, OMul | OLow, OLow | OSx, OSx
  | OLtu, OLtu | OLts, OLts | ODivU, ODivU | ORemU, ORemU | OShl, OShl => true
  | _, _ => false
  end.

Definition opk_idx (o : opk) : Z :=
  match o with
  | OAnd => 0 | OOr => 1 | OXor => 2 | OShr => 3 | OMul => 4 | OLow => 5 | OSx => 6
  | OLtu => 7 | OLts => 8 | ODivU => 9 | ORemU => 10 | OShl => 11
  end.

Fixpoint expr_eqb (x y : expr) : bool :=
  match x, y with
  | ELit a, ELit b => Z.eqb a b
  | EZv a, EZv b => Pos.eqb a b
  | EUv a, EUv b => Pos.eqb a b
  | EAdd a b, EAdd a' b' => expr_eqb a a' && expr_eqb b b'
  | EMulC c a, EMulC c' a' => Z.eqb c c' && expr_eqb a a'
  | EOp o a b, EOp o' a' b' => opk_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | _, _ => false
  end.

Definition sreg_eqb (x y : sreg) : bool :=
  match x, y with
  | RW a, RW b => Pos.eqb a b
  | RZ a, RZ b => expr_eqb a b
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition ctag (e : expr) : Z :=
  match e with ELit _ => 0 | EZv _ => 1 | EUv _ => 2 | EOp _ _ _ => 3 | EMulC _ _ => 4 | EAdd _ _ => 5 end.

Definition lex (c : comparison) (k : comparison) : comparison :=
  match c with Eq => k | _ => c end.

Fixpoint expr_cmp (x y : expr) : comparison :=
  match x, y with
  | ELit a, ELit b => Z.compare a b
  | EZv a, EZv b => Pos.compare a b
  | EUv a, EUv b => Pos.compare a b
  | EAdd a b, EAdd a' b' => lex (expr_cmp a a') (expr_cmp b b')
  | EMulC c a, EMulC c' a' => lex (Z.compare c c') (expr_cmp a a')
  | EOp o a b, EOp o' a' b' => lex (Z.compare (opk_idx o) (opk_idx o')) (lex (expr_cmp a a') (expr_cmp b b'))
  | _, _ => Z.compare (ctag x) (ctag y)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition terms := list (Z * expr).

(* [comment removed for export] *)
Fixpoint lin_of (e : expr) : terms * Z :=
  match e with
  | ELit c => ([], c)
  | EAdd (EMulC k a) rest => let '(ts, c) := lin_of rest in ((k, a) :: ts, c)
  | _ => ([(1, e)], 0)
  end.

Fixpoint of_terms (ts : terms) (c : Z) : expr :=
  match ts with
  | [] => ELit c
  | (k, a) :: ts' => EAdd (EMulC k a) (of_terms ts' c)
  end.

(* [comment removed for export] *)
Fixpoint terms_add (xs : terms) : terms -> terms :=
  match xs with
  | [] => fun ys => ys
  | (k, a) :: xs' =>
      fix go (ys : terms) : terms :=
        match ys with
        | [] => xs
        | (k', a') :: ys' =>
            match expr_cmp a a' with
            | Lt => (k, a) :: terms_add xs' ys
            | Gt => (k', a') :: go ys'
            | Eq => let s := k + k' in
                    if Z.eqb s 0 then terms_add xs' ys' else (s, a) :: terms_add xs' ys'
            end
        end
  end.

Definition terms_scale (k : Z) (xs : terms) : terms :=
  if Z.eqb k 0 then [] else map (fun '(c, a) => (k * c, a)) xs.

(* [comment removed for export] *)
Definition eadd (a b : expr) : expr :=
  let '(xs, c) := lin_of a in let '(ys, d) := lin_of b in of_terms (terms_add xs ys) (c + d).

Definition emulc (k : Z) (a : expr) : expr :=
  let '(xs, c) := lin_of a in of_terms (terms_scale k xs) (k * c).

Definition esub (a b : expr) : expr := eadd a (emulc (-1) b).

Definition eaddc (a : expr) (k : Z) : expr := eadd a (ELit k).

(* [comment removed for export] *)
Definition eatom (a : expr) : expr := EAdd (EMulC 1 a) (ELit 0).

Definition is_lit (e : expr) : option Z :=
  match e with ELit z => Some z | _ => None end.

(* [comment removed for export] *)
Definition econst (e : expr) : Z := snd (lin_of e).
Definition ebase (e : expr) : expr := of_terms (fst (lin_of e)) 0.

(* [comment removed for export] *)
Fixpoint terms_eqb (xs ys : terms) : bool :=
  match xs, ys with
  | [], [] => true
  | (k, a) :: xs', (k', a') :: ys' => Z.eqb k k' && expr_eqb a a' && terms_eqb xs' ys'
  | _, _ => false
  end.

Definition ediff_lit (a b : expr) : option Z :=
  let '(xs, c) := lin_of a in let '(ys, d) := lin_of b in
  if terms_eqb xs ys then Some (c - d) else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition expr_of_reg (r : sreg) : expr :=
  match r with RW i => eatom (EUv i) | RZ e => e end.

(* [comment removed for export] *)
Definition mkreg (e : expr) : sreg :=
  match e with
  | EAdd (EMulC 1 (EUv i)) (ELit 0) => RW i
  | _ => RZ e
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record oracle := ORA { o_ge : expr -> bool; o_al : expr -> N;
                       (* [comment removed for export] *)
                       o_kn : expr -> bool }.

Definition two64 : Z := 0x10000000000000000.
Definition two63 : Z := 0x8000000000000000.
Definition two32 : Z := 0x100000000.
Definition two31 : Z := 0x80000000.

(* [comment removed for export] *)
Definition e_in (O : oracle) (e : expr) (lo hi : Z) : bool :=
  if o_ge O (eadd e (ELit (- lo))) then o_ge O (eadd (emulc (-1) e) (ELit hi)) else false.

(* [comment removed for export] *)
Ltac unlazy1_in H :=
  match type of H with
  | context [if ?c then ?d else false] => change (if c then d else false) with (andb c d) in H
  | context [if ?c then true else ?d] => change (if c then true else d) with (orb c d) in H
  end.
Ltac unlazy1 :=
  match goal with
  | |- context [if ?c then ?d else false] => change (if c then d else false) with (andb c d)
  | |- context [if ?c then true else ?d] => change (if c then true else d) with (orb c d)
  end.

Definition e_u64 (O : oracle) (e : expr) : bool := e_in O e 0 (two64 - 1).
Definition e_s32 (O : oracle) (e : expr) : bool := e_in O e (- two31) (two31 - 1).

(* [comment removed for export] *)
Fixpoint pctz (p : positive) : N :=
  match p with xO q => N.succ (pctz q) | _ => 0%N end.
Definition zal (z : Z) : N :=
  match z with Z0 => 64%N | Zpos p | Zneg p => pctz p end.

(* [comment removed for export] *)
Fixpoint xal (O : oracle) (e : expr) : N :=
  match e with
  | ELit c => zal c
  | EZv _ | EUv _ => o_al O e
  | EAdd a b => N.min (xal O a) (xal O b)
  | EMulC k a => (zal k + xal O a)%N
  | EOp OOr a b => N.max (o_al O e) (N.min (xal O a) (xal O b))
  | EOp OAnd a b => N.max (o_al O e) (N.max (xal O a) (xal O b))
  | EOp _ _ _ => o_al O e
  end.

Fixpoint terms_al (O : oracle) (ts : terms) : N :=
  match ts with
  | [] => 64%N
  | (k, a) :: ts' => N.min (zal k + xal O a)%N (terms_al O ts')
  end.

Definition eal (O : oracle) (e : expr) : N :=
  let '(ts, c) := lin_of e in N.min (terms_al O ts) (zal c).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zlow (k : Z) (x : Z) : Z := x mod 2 ^ k.
Definition zswrap (k : Z) (x : Z) : Z := (x + 2 ^ (k - 1)) mod 2 ^ k - 2 ^ (k - 1).

(* [comment removed for export] *)
Definition elow (O : oracle) (e : expr) (k : Z) : expr :=
  match is_lit e with
  | Some x => ELit (zlow k x)
  | None => if e_in O e 0 (2 ^ k - 1) then e else eatom (EOp OLow e (ELit k))
  end.

(* [comment removed for export] *)
Definition esx (O : oracle) (e : expr) (k : Z) : expr :=
  match is_lit e with
  | Some x => ELit (zswrap k x)
  | None => if e_in O e (- 2 ^ (k - 1)) (2 ^ (k - 1) - 1) then e
            else eatom (EOp OSx e (ELit k))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ew32 (O : oracle) (e : expr) : expr :=
  match is_lit e with
  | Some x => ELit (zswrap 32 x)
  | None =>
      let e2 := eadd (ebase e) (ELit (zswrap 32 (econst e))) in
      if e_s32 O e2 then e2 else if e_s32 O e then e else esx O (elow O e 32) 32
  end.

(* [comment removed for export] *)
Definition eshr (O : oracle) (e : expr) (k : Z) : expr :=
  if Z.eqb k 0 then e else
  match is_lit e with
  | Some x => ELit (Z.shiftr (zlow 64 x) k)
  | None => let e' := elow O e 64 in eatom (EOp OShr e' (ELit k))
  end.

(* [comment removed for export] *)
Definition olit_eqb (o : option Z) (z : Z) : bool :=
  match o with Some x => Z.eqb x z | None => false end.

(* [comment removed for export] *)
Definition low_mask_j (m : Z) : option Z :=
  if Z.ltb 0 m && Z.eqb (Z.land m (m + 1)) 0 then Some (Z.log2 (m + 1)) else None.
(* [comment removed for export] *)
Definition high_mask_j (m : Z) : option Z :=
  if Z.ltb m (-1) && Z.eqb (Z.land (- m) (- m - 1)) 0 then Some (Z.log2 (- m)) else None.

Definition eand (O : oracle) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (Z.land x y)
  | _, _ =>
      if olit_eqb (is_lit b) (-1) then a
      else if olit_eqb (is_lit a) (-1) then b
      else if olit_eqb (is_lit b) 0 || olit_eqb (is_lit a) 0 then ELit 0
      else match is_lit b with
           | Some m =>
               match low_mask_j m with
               | Some j =>
                   (* [comment removed for export] *)
                   if N.leb (Z.to_N j) (eal O a) then ELit 0
                   else if e_in O a 0 m then a
                   else eatom (EOp OAnd a b)
               | None =>
                   match high_mask_j m with
                   | Some j => if N.leb (Z.to_N j) (eal O a) then a else eatom (EOp OAnd a b)
                   | None => eatom (EOp OAnd a b)
                   end
               end
           | None => if expr_eqb a b then a else eatom (EOp OAnd a b)
           end
  end.

(* [comment removed for export] *)
Definition eor (O : oracle) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (Z.lor x y)
  | _, Some 0 => a
  | Some 0, _ => b
  | _, Some y => if Z.ltb 0 y && Z.ltb y (2 ^ Z.of_N (eal O a)) then eadd a (ELit y) else eatom (EOp OOr a b)
  | _, _ => if expr_eqb a b then a else eatom (EOp OOr a b)
  end.

(* [comment removed for export] *)
Definition exor (O : oracle) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, Some y => ELit (Z.lxor x y)
  | _, Some 0 => a
  | Some 0, _ => b
  | _, Some y => if Z.eqb (zlow 64 y) (two64 - 1)
                 then (if e_u64 O a then eadd (ELit (two64 - 1)) (emulc (-1) a) else eadd (ELit (-1)) (emulc (-1) a))
                 else eatom (EOp OXor a b)
  | _, _ => eatom (EOp OXor a b)
  end.

(* [comment removed for export] *)
Definition omul (a b : expr) : expr :=
  match expr_cmp a b with Gt => EOp OMul b a | _ => EOp OMul a b end.
Definition emul (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, _ => emulc x b
  | _, Some y => emulc y a
  | _, _ => eatom (EOp OMul a b)
  end.
(* [comment removed for export] *)
Definition emulO (O : oracle) (a b : expr) : expr :=
  match is_lit a, is_lit b with
  | Some x, _ => emulc x b
  | _, Some y => emulc y a
  | _, _ => if o_kn O (EOp OMul b a) then eatom (EOp OMul b a) else eatom (EOp OMul a b)
  end.

(* [comment removed for export] *)
Definition eshl (a : expr) (k : Z) : expr := emulc (2 ^ k) a.

(* [comment removed for export] *)
Fixpoint lexistsb {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with [] => false | x :: l' => if f x then true else lexistsb f l' end.
Fixpoint lforallb {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with [] => true | x :: l' => if f x then lforallb f l' else false end.
