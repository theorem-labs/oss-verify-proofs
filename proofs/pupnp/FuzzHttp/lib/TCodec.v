(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Ltac2 Require Import Ltac2.
From Stdlib Require Import BinNums.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac2 Type exn ::= [ TCDecode (string) ].
Ltac2 fail0 (m : string) := Control.throw (TCDecode m).
Ltac2 Type rd := { str : string; mutable pos : int }.
Ltac2 getc (r : rd) : int := let c := Char.to_int (String.get (r.(str)) (r.(pos))) in r.(pos) := Int.add (r.(pos)) 1; c.
Ltac2 rec num_acc (r : rd) (acc : int) : int :=
let c := getc r in
if Int.le 80 c then (if Int.lt c 112 then num_acc r (Int.add (Int.mul acc 32) (Int.sub c 80)) else fail0 "digit")
else if Int.le 48 c then Int.add (Int.mul acc 32) (Int.sub c 48) else fail0 "digit".
Ltac2 num (r : rd) : int := num_acc r 0.
Ltac2 rec digits (r : rd) (acc : int list) : int list :=
let c := getc r in
if Int.le 80 c then digits r (Int.sub c 80 :: acc) else List.rev (Int.sub c 48 :: acc).
Ltac2 rec bits5 (d : int) (k : int) (acc : bool list) : bool list :=
if Int.equal k 0 then acc else bits5 (Int.div d 2) (Int.sub k 1) (Int.equal (Int.mod d 2) 1 :: acc).
Ltac2 rec pos_of_bits (t : constr option) (bs : bool list) : constr :=
match bs with
| [] => match t with Some t => t | None => fail0 "zero positive" end
| b :: bs' =>
match t with
| None => if b then pos_of_bits (Some 'xH) bs' else pos_of_bits None bs'
| Some t => pos_of_bits (Some (Constr.Unsafe.make (Constr.Unsafe.App (if b then 'xI else 'xO) [| t |]))) bs'
end
end.
Ltac2 pos (r : rd) : constr := pos_of_bits None (List.flat_map (fun d => bits5 d 5 []) (digits r [])).
Ltac2 rec nat_of (k : int) (t : constr) : constr := if Int.equal k 0 then t else nat_of (Int.sub k 1) (Constr.Unsafe.make (Constr.Unsafe.App 'S [| t |])).
Ltac2 app1 (f : constr) (x : constr) : constr := Constr.Unsafe.make (Constr.Unsafe.App f [| x |]).
Ltac2 rec split_dot (s : string) (i : int) (j : int) (acc : ident list) : ident list :=
let mk a b := match Ident.of_string (String.sub s a (Int.sub b a)) with Some id => id | None => fail0 "ident" end in
if Int.equal j (String.length s) then List.rev (mk i j :: acc)
else if Int.equal (Char.to_int (String.get s j)) 46 then split_dot s (Int.add j 1) (Int.add j 1) (mk i j :: acc)
else split_dot s i (Int.add j 1) acc.
Ltac2 rec nth_s (l : 'a list) (i : int) (d : 'a) : 'a := match l with [] => d | x :: t => if Int.equal i 0 then x else nth_s t (Int.sub i 1) d end.
Ltac2 rec assoc (l : (int * constr) list) (j : int) : constr option :=
match l with [] => None | (k, c) :: t => if Int.equal k j then Some c else assoc t j end.
Ltac2 Type dt := { nm : int -> string; mutable rc : (int * constr) list }.
Ltac2 gref (t : dt) (j : int) : constr :=
match assoc (t.(rc)) j with
| Some c => c
| None =>
let s := t.(nm) j in
match Env.get (split_dot s 0 0 []) with
| Some r => let c := Env.instantiate r in t.(rc) := (j, c) :: t.(rc); c
| None => fail0 (String.app "name " s)
end
end.
Ltac2 gid (t : dt) (j : int) : ident := match Ident.of_string (t.(nm) j) with Some i => i | None => fail0 "ident" end.
Ltac2 gind (t : dt) (j : int) : inductive :=
match Constr.Unsafe.kind (gref t j) with Constr.Unsafe.Ind i _ => i | _ => fail0 "not an inductive" end.
Ltac2 binder_of (t : dt) (b : int) (ty : constr) : binder :=
let nm := if Int.lt b 2 then None else Some (gid t (Int.sub (Int.div b 2) 1)) in
Constr.Binder.unsafe_make nm (if Int.equal (Int.mod b 2) 1 then Constr.Relevance.irrelevant else Constr.Relevance.relevant) ty.
Ltac2 rel_of (k : int) := if Int.equal k 1 then Constr.Relevance.irrelevant else Constr.Relevance.relevant.
Ltac2 rec nodes_list (r : rd) (k : int) (acc : int list) : int list := if Int.equal k 0 then List.rev acc else nodes_list r (Int.sub k 1) (num r :: acc).
Ltac2 decode_dt (t : dt) (s : string) : constr :=
let r := { str := s; pos := 0 } in
let n := num r in
let a := Array.make n 'Prop in
let rec go (i : int) :=
if Int.equal i n then Array.get a (Int.sub n 1) else
let ch (d : int) := Array.get a (Int.sub i d) in
let c := getc r in
let v :=
if Int.equal c 114 then Constr.Unsafe.make (Constr.Unsafe.Rel (num r))
else if Int.equal c 118 then Constr.Unsafe.make (Constr.Unsafe.Var (gid t (num r)))
else if Int.equal c 33 then 'Prop else if Int.equal c 35 then 'Set else if Int.equal c 36 then 'SProp
else if Int.equal c 112 then let b := num r in let x := num r in let y := num r in Constr.Unsafe.make (Constr.Unsafe.Prod (binder_of t b (ch x)) (ch y))
else if Int.equal c 113 then let b := num r in let x := num r in let y := num r in Constr.Unsafe.make (Constr.Unsafe.Lambda (binder_of t b (ch x)) (ch y))
else if Int.equal c 116 then let b := num r in let x := num r in let w := num r in let y := num r in
Constr.Unsafe.make (Constr.Unsafe.LetIn (binder_of t b (ch x)) (ch w) (ch y))
else if Int.equal c 37 then let f := num r in let k := num r in
Constr.Unsafe.make (Constr.Unsafe.App (ch f) (Array.of_list (List.map ch (nodes_list r k []))))
else if Int.equal c 38 then gref t (num r) else if Int.equal c 39 then gref t (num r) else if Int.equal c 40 then gref t (num r)
else if Int.equal c 41 then
let j := num r in let rl := num r in let x := num r in let y := num r in let k := num r in
let bs := Array.of_list (List.map ch (nodes_list r k [])) in
Constr.Unsafe.make (Constr.Unsafe.Case (Constr.Unsafe.case (gind t j)) (ch x, rel_of rl) Constr.Unsafe.NoInvert (ch y) bs)
else if Int.equal c 42 then
let j := num r in let idx := num r in let unf := num r in let rl := num r in let y := num r in
let p := match Ind.get_projections (Ind.data (gind t j)) with Some ps => Array.get ps idx | None => fail0 "projections" end in
Constr.Unsafe.make (Constr.Unsafe.Proj (Proj.set_unfolded p (Int.equal unf 1)) (rel_of rl) (ch y))
else if Int.equal c 47 then let k := num r in let x := num r in let y := num r in
Constr.Unsafe.make (Constr.Unsafe.Cast (ch x) (if Int.equal k 0 then Constr.Cast.default else if Int.equal k 1 then Constr.Cast.vm else Constr.Cast.native) (ch y))
else if Int.equal c 43 then app1 'Zpos (pos r) else if Int.equal c 45 then app1 'Zneg (pos r)
else if Int.equal c 122 then 'Z0 else if Int.equal c 119 then 'N0 else if Int.equal c 121 then app1 'Npos (pos r)
else if Int.equal c 120 then pos r else if Int.equal c 117 then nat_of (num r) 'O
else fail0 "tag" in
Array.set a i v; go (Int.add i 1) in
go 0.
Ltac2 name2 (pre : string list) (bk : string list list) (i : int) : string :=
let e := nth_s (nth_s bk (Int.div i 16) []) (Int.mod i 16) "" in
if Int.equal (String.length e) 0 then fail0 "name index" else
String.app (nth_s pre (Int.sub (Char.to_int (String.get e 0)) 48) "") (String.sub e 1 (Int.sub (String.length e) 1)).
Ltac2 decode2 (tab : unit -> string list * string list list) (s : string) : constr :=
let (pre, bk) := tab () in decode_dt { nm := name2 pre bk; rc := [] } s.
Ltac2 tc2 (tab : unit -> string list * string list list) (s : string) : unit :=
let t := decode2 tab s in
match Constr.Unsafe.check t with Val t' => exact $t' | Err e => Control.throw e end.
