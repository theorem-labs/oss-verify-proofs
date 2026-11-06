(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2 Int Char String.

Ltac2 mutable tbl : unit -> string := fun () => "".

Ltac2 Type hint := [ HFail | HKeep (string list) ].

Ltac2 d64 (s : string) (p : int) : int := Int.sub (Char.to_int (String.get s p)) 48.
Ltac2 rd2 (s : string) (p : int) : int := Int.add (Int.mul (d64 s p) 64) (d64 s (Int.add p 1)).
Ltac2 rd3 (s : string) (p : int) : int := Int.add (Int.mul (rd2 s p) 64) (d64 s (Int.add p 2)).

Ltac2 rec bsearch (s : string) (key : string) (kw : int) (lo : int) (hi : int) : int :=
  if Int.lt hi lo then -1 else
  let mid := Int.asr (Int.add lo hi) 1 in
  let c := String.compare (String.sub s (Int.add 5 (Int.mul mid kw)) kw) key in
  if Int.equal c 0 then mid
  else if Int.lt c 0 then bsearch s key kw (Int.add mid 1) hi
  else bsearch s key kw lo (Int.sub mid 1).

Ltac2 rec names (s : string) (p : int) (e : int) (acc : string list) : string list :=
  if Int.le e p then List.rev acc
  else let l := d64 s p in names s (Int.add (Int.add p 1) l) e (String.sub s (Int.add p 1) l :: acc).

Ltac2 lookup_in (s : string) (d : string) : hint option :=
  let ls := String.length s in
  if Int.lt ls 5 then None else
  let n := rd3 s 0 in
  let kw := rd2 s 3 in
  let ld := String.length d in
  if Int.lt kw ld then None else
  let key := if Int.equal kw ld then d else String.app d (String.make (Int.sub kw ld) (Char.of_int 32)) in
  let i := bsearch s key kw 0 (Int.sub n 1) in
  if Int.lt i 0 then None else
  let ob := Int.add 5 (Int.mul n kw) in
  let pb := Int.add ob (Int.mul 3 (Int.add n 1)) in
  let o1 := Int.add pb (rd3 s (Int.add ob (Int.mul 3 i))) in
  let o2 := Int.add pb (rd3 s (Int.add ob (Int.mul 3 (Int.add i 1)))) in
  if Int.equal (Char.to_int (String.get s o1)) 70 (* [comment removed for export] *) then Some HFail
  else Some (HKeep (names s (Int.add o1 1) o2 [])).

(* [comment removed for export] *)
Ltac2 lookup (d : string) : hint option := lookup_in (tbl ()) d.
