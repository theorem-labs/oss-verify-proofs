(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Inductive item : Type :=
| IK (off : Z) (ws : list Z) (tl : list Z)   (* [comment removed for export] *)
| IV (off : Z) (l : lin) (j n : Z).          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ent : Type := (Z * bval)%type.
Fixpoint merge (a : list ent) : list ent -> list ent :=
  fix aux (b : list ent) : list ent :=
    match a, b with
    | [], _ => b
    | _, [] => a
    | x :: a', y :: b' => if Z.leb (fst x) (fst y) then x :: merge a' b else y :: aux b'
    end.
Fixpoint merge_pairs (ls : list (list ent)) : list (list ent) :=
  match ls with a :: b :: r => merge a b :: merge_pairs r | _ => ls end.
Fixpoint msort_f (fuel : nat) (ls : list (list ent)) : list ent :=
  match fuel with
  | O => List.concat ls
  | S f => match ls with [] => [] | [a] => a | _ => msort_f f (merge_pairs ls) end
  end.
Definition msort (l : list ent) : list ent := msort_f 64 (List.map (fun x => [x]) l).

(* [comment removed for export] *)
Fixpoint tents {A} (t : tree A) (k : positive -> positive) (acc : list (positive * A)) : list (positive * A) :=
  match t with
  | TEmpty => acc
  | TNode l v r => tents l (fun p => k (xO p)) (tents r (fun p => k (xI p)) (match v with Some x => (k xH, x) :: acc | None => acc end))
  end.
Definition cont_ents (t : tree bval) : list ent := msort (List.map (fun '(p, v) => (Z.pos p - 1, v)) (tents t (fun p => p) [])).

(* [comment removed for export] *)
Inductive brun : Type := BRK (off : Z) (rev_bs : list Z) | BRV (off : Z) (l : lin) (j n : Z).
Definition brun_next (r : brun) : Z := match r with BRK o bs => o + Z.of_nat (List.length bs) | BRV o _ _ n => o + n end.
(* [comment removed for export] *)
Fixpoint runs (es : list ent) (cur : option (brun * Z)) (acc : list brun) : list brun :=
  match es with
  | [] => match cur with Some (r, _) => r :: acc | None => acc end
  | (o, v) :: es' =>
      match cur, v with
      | Some (BRK o0 bs, nx), BK b => if Z.eqb o nx then runs es' (Some (BRK o0 (b :: bs), nx + 1)) acc
                                      else runs es' (Some (BRK o [b], o + 1)) (BRK o0 bs :: acc)
      | Some (BRV o0 l j n, nx), BV l' j' => if (Z.eqb o nx && Z.eqb j' (j + n) && lin_eqb l l')%bool then runs es' (Some (BRV o0 l j (n + 1), nx + 1)) acc
                                             else runs es' (Some (BRV o l' j' 1, o + 1)) (BRV o0 l j n :: acc)
      | Some (r, _), BK b => runs es' (Some (BRK o [b], o + 1)) (r :: acc)
      | Some (r, _), BV l' j' => runs es' (Some (BRV o l' j' 1, o + 1)) (r :: acc)
      | None, BK b => runs es' (Some (BRK o [b], o + 1)) acc
      | None, BV l' j' => runs es' (Some (BRV o l' j' 1, o + 1)) acc
      end
  end.
Fixpoint pack8 (bs : list Z) : list Z * list Z :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r =>
      let '(ws, tl) := pack8 r in
      ((b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) :: ws, tl)
  | _ => ([], bs)
  end.
Definition item_of (r : brun) : item :=
  match r with
  | BRK o rbs => let '(ws, tl) := pack8 (List.rev' rbs) in IK o ws tl
  | BRV o l j n => IV o l j n
  end.
Definition enc_cont (t : tree bval) : list item := List.rev' (List.map item_of (runs (cont_ents t) None [])).

(* [comment removed for export] *)
Definition unpack8 (w : Z) : list Z :=
  [Z.land w 255; Z.land (Z.shiftr w 8) 255; Z.land (Z.shiftr w 16) 255; Z.land (Z.shiftr w 24) 255;
   Z.land (Z.shiftr w 32) 255; Z.land (Z.shiftr w 40) 255; Z.land (Z.shiftr w 48) 255; Z.land (Z.shiftr w 56) 255].
Fixpoint put_ks (bs : list Z) (o : Z) (t : tree bval) : tree bval :=
  match bs with [] => t | b :: r => put_ks r (o + 1) (tset (okey o) (BK b) t) end.
Fixpoint put_ws (ws : list Z) (o : Z) (t : tree bval) : tree bval :=
  match ws with [] => t | w :: r => put_ws r (o + 8) (put_ks (unpack8 w) o t) end.
Fixpoint put_vs (n : nat) (l : lin) (j o : Z) (t : tree bval) : tree bval :=
  match n with O => t | S n' => put_vs n' l (j + 1) (o + 1) (tset (okey o) (BV l j) t) end.
Definition dec_item (t : tree bval) (i : item) : tree bval :=
  match i with
  | IK o ws tl => put_ks tl (o + 8 * Z.of_nat (List.length ws)) (put_ws ws o t)
  | IV o l j n => put_vs (Z.to_nat n) l j o t
  end.
Definition dec_cont (is : list item) : tree bval := List.fold_left dec_item is TEmpty.

(* [comment removed for export] *)
Definition erg : Type := (lin * lin * rkind * list item)%type.
Definition enc_rg (R : region) : erg := (rg_base R, rg_size R, rg_kind R, enc_cont (rg_cont R)).
Definition dec_rg (e : erg) : region := let '(b, z, k, is) := e in RG b z k (dec_cont is).
Definition est : Type := (Z * list (positive * lin) * list erg * list fact * positive * rsv)%type.
Definition enc_st (S : sst) : est :=
  (s_pc S, tents (s_regs S) (fun p => p) [], List.map enc_rg (s_rgs S), s_facts S, s_next S, s_resv S).
Definition dec_st (e : est) : sst :=
  let '(pc, regs, rgs, fs, nx, rv) := e in
  SST pc (List.fold_left (fun t '(k, v) => tset k v t) regs TEmpty) (List.map dec_rg rgs) fs nx rv.

(* [comment removed for export] *)
Fixpoint tree_sub {A} (f : A -> A -> bool) (t u : tree A) (k : positive -> positive) : bool :=
  match t with
  | TEmpty => true
  | TNode l v r => (match v with Some x => match tget (k xH) u with Some y => f x y | None => false end | None => true end &&
                    tree_sub f l u (fun p => k (xO p)) && tree_sub f r u (fun p => k (xI p)))%bool
  end.
Definition bval_eqb (a b : bval) : bool :=
  match a, b with BK x, BK y => Z.eqb x y | BV l j, BV l' j' => (lin_eqb l l' && Z.eqb j j')%bool | _, _ => false end.
Definition rg_same (R R' : region) : bool :=
  (lin_eqb (rg_base R) (rg_base R') && lin_eqb (rg_size R) (rg_size R') &&
   tree_sub bval_eqb (rg_cont R) (rg_cont R') (fun p => p) && tree_sub bval_eqb (rg_cont R') (rg_cont R) (fun p => p))%bool.
Fixpoint rgs_same (a b : list region) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => (rg_same x y && rgs_same a' b')%bool | _, _ => false end.
Definition st_same (S S' : sst) : bool :=
  (Z.eqb (s_pc S) (s_pc S') && tree_sub lin_eqb (s_regs S) (s_regs S') (fun p => p) && tree_sub lin_eqb (s_regs S') (s_regs S) (fun p => p) &&
   rgs_same (s_rgs S) (s_rgs S') && Pos.eqb (s_next S) (s_next S') && Nat.eqb (List.length (s_facts S)) (List.length (s_facts S')))%bool.
