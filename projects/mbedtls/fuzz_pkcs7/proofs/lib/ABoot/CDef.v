(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith.
From Ltac2 Require Import Ltac2 Constr Env Std String Char Int List Message Ident Control Array.

Ltac2 Type rstate := { src : string; mutable pos : int; globs : constr array;
                       kxI : constr; kxO : constr; kxH : constr; kZ0 : constr; kZpos : constr; kZneg : constr;
                       kS : constr; kO : constr; kN0 : constr; kNpos : constr }.

Ltac2 fail (msg : string) : 'a := Control.throw (Invalid_argument (Some (Message.of_string msg))).

Ltac2 rec split_from (s : string) (sep : int) (i : int) (start : int) (acc : string list) : string list :=
  let n := String.length s in
  if Int.equal i n then List.rev (String.sub s start (Int.sub i start) :: acc)
  else if Int.equal (Char.to_int (String.get s i)) sep then
    split_from s sep (Int.add i 1) (Int.add i 1) (String.sub s start (Int.sub i start) :: acc)
  else split_from s sep (Int.add i 1) start acc.
Ltac2 split_on (s : string) (sep : int) : string list := split_from s sep 0 0 [].

Ltac2 global_of_path (p : string) : constr :=
  let ids := List.map (fun s => match Ident.of_string s with Some i => i | None => fail (String.app "CDef: bad identifier in " p) end)
                      (split_on p 46) in
  match Env.get ids with
  | Some r => Env.instantiate r
  | None => fail (String.app "CDef: no such global " p)
  end.

Ltac2 app1 (f : constr) (a : constr) : constr := Constr.Unsafe.make (Constr.Unsafe.App f (Array.of_list [a])).

Ltac2 peek (st : rstate) : int := Char.to_int (String.get (st.(src)) (st.(pos))).
Ltac2 adv (st : rstate) : unit := st.(pos) := Int.add (st.(pos)) 1.

(* [comment removed for export] *)
Ltac2 rec digits (st : rstate) (acc : int list) : int list :=
  let c := peek st in
  adv st;
  if Int.equal c 46 then List.rev acc
  else if Bool.and (Int.le 48 c) (Int.le c 63) then digits st (Int.sub c 48 :: acc)
  else fail "CDef: bad digit".

Ltac2 int_of_digits (ds : int list) : int := List.fold_left (fun acc d => Int.add (Int.mul acc 16) d) 0 ds.

Ltac2 pos_of_digits (st : rstate) (ds : int list) : constr :=
  let step (cur : constr option) (bit : bool) :=
    match cur with
    | None => if bit then Some (st.(kxH)) else None
    | Some c => Some (app1 (if bit then st.(kxI) else st.(kxO)) c)
    end in
  let dig (cur : constr option) (d : int) :=
    let cur := step cur (Int.equal (Int.land d 8) 8) in
    let cur := step cur (Int.equal (Int.land d 4) 4) in
    let cur := step cur (Int.equal (Int.land d 2) 2) in
    step cur (Int.equal (Int.land d 1) 1) in
  match List.fold_left dig None ds with
  | Some c => c
  | None => fail "CDef: zero positive"
  end.

Ltac2 rec nat_chain (st : rstate) (n : int) (c : constr) : constr :=
  if Int.equal n 0 then c else nat_chain st (Int.sub n 1) (app1 (st.(kS)) c).

Ltac2 rec term (st : rstate) : constr :=
  let c := peek st in
  adv st;
  if Int.equal c 40 then                                   (* [comment removed for export] *)
    let f := Array.get (st.(globs)) (int_of_digits (digits st [])) in
    let args := arglist st [] in
    Constr.Unsafe.make (Constr.Unsafe.App f (Array.of_list args))
  else if Int.equal c 36 then Array.get (st.(globs)) (int_of_digits (digits st []))     (* [comment removed for export] *)
  else if Int.equal c 61 then st.(kZ0)                                                    (* [comment removed for export] *)
  else if Int.equal c 43 then app1 (st.(kZpos)) (pos_of_digits st (digits st []))         (* [comment removed for export] *)
  else if Int.equal c 45 then app1 (st.(kZneg)) (pos_of_digits st (digits st []))         (* [comment removed for export] *)
  else if Int.equal c 94 then pos_of_digits st (digits st [])                             (* [comment removed for export] *)
  else if Int.equal c 35 then nat_chain st (int_of_digits (digits st [])) (st.(kO))       (* [comment removed for export] *)
  else if Int.equal c 126 then st.(kN0)                                                  (* [comment removed for export] *)
  else if Int.equal c 38 then app1 (st.(kNpos)) (pos_of_digits st (digits st []))        (* [comment removed for export] *)
  else fail "CDef: bad tag"
with arglist (st : rstate) (acc : constr list) : constr list :=
  if Int.equal (peek st) 41 then (adv st; List.rev acc)
  else let a := term st in arglist st (a :: acc).

Ltac2 decode (table : constr list) (body : string) : constr :=
  let globs := Array.of_list table in
  let g := global_of_path in
  let st := { src := body; pos := 0; globs := globs;
              kxI := g "Corelib.Numbers.BinNums.xI"; kxO := g "Corelib.Numbers.BinNums.xO"; kxH := g "Corelib.Numbers.BinNums.xH";
              kZ0 := g "Corelib.Numbers.BinNums.Z0"; kZpos := g "Corelib.Numbers.BinNums.Zpos"; kZneg := g "Corelib.Numbers.BinNums.Zneg";
              kS := g "Corelib.Init.Datatypes.S"; kO := g "Corelib.Init.Datatypes.O";
              kN0 := g "Corelib.Numbers.BinNums.N0"; kNpos := g "Corelib.Numbers.BinNums.Npos" } in
  let t := term st in
  if Int.equal (st.(pos)) (String.length body) then t else fail "CDef: trailing characters".

(* [comment removed for export] *)
Ltac2 build (table : constr list) (body : string) : unit :=
  let t := decode table body in
  Control.refine (fun () => t).
