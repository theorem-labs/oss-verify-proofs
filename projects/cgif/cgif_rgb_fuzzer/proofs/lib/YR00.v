(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Ltac2 Require Import Ltac2 Constr Message Ref.
From Stdlib Require Import BinNums.
Set Default Proof Mode "Classic".
Ltac2 rec nth_limbs (p : constr) (acc : int list) (cur : int) (bit : int) : (int list) option :=
match Unsafe.kind p with
| Unsafe.Constructor _ _ =>
if Constr.equal p 'xH then Some (List.rev ((Int.add cur (Int.lsl 1 bit)) :: acc)) else None
| Unsafe.App f args =>
if Int.equal (Array.length args) 1 then
let a := Array.get args 0 in
let (d, ok) := if Constr.equal f 'xO then (0, true) else if Constr.equal f 'xI then (1, true) else (0, false) in
if ok then
let cur := Int.add cur (Int.lsl d bit) in
if Int.equal bit 29 then nth_limbs a (cur :: acc) 0 0 else nth_limbs a acc cur (Int.add bit 1)
else None
else None
| _ => None
end.
Ltac2 small_of_limbs (l : int list) : int option :=
match l with
| [a] => Some a
| [a; b] => if Int.lt b 536870912 then Some (Int.add a (Int.lsl b 30)) else None
| _ => None
end.
Ltac2 rec nat_val (c : constr) (n : int) : int option :=
match Unsafe.kind c with
| Unsafe.Constructor _ _ => if Constr.equal c 'O then Some n else None
| Unsafe.App f args => if Bool.and (Constr.equal f 'S) (Int.equal (Array.length args) 1) then nat_val (Array.get args 0) (Int.add n 1) else None
| _ => None
end.
Ltac2 rec index_of (h : constr) (l : constr list) (i : int) : int option :=
match l with [] => None | x :: r => if Constr.equal x h then Some i else index_of h r (Int.add i 1) end.
Ltac2 is_type (c : constr) : bool :=
match Unsafe.kind (Constr.type c) with Unsafe.Sort _ => true | _ => false end.
Ltac2 encode_exn (c0 : constr) : unit :=
let heads : constr list Ref.ref := Ref.ref [] in
let nty : (constr * int) list Ref.ref := Ref.ref [] in
let out : int list Ref.ref := Ref.ref [] in
let emit (i : int) := Ref.set out (i :: Ref.get out) in
let head_index (h : constr) : int :=
match index_of h (List.rev (Ref.get heads)) 0 with
| Some i => i
| None => Ref.set heads (h :: Ref.get heads); Int.sub (List.length (Ref.get heads)) 1
end in
let rec lead_types (args : constr array) (i : int) : int :=
if Int.lt i (Array.length args) then (if is_type (Array.get args i) then lead_types args (Int.add i 1) else i) else i in
let ntypes (f : constr) (args : constr array) : int :=
let rec find l := match l with [] => None | (x, n) :: r => if Constr.equal x f then Some n else find r end in
match find (Ref.get nty) with
| Some n => if Int.le n (Array.length args) then n else Array.length args
| None => let n := lead_types args 0 in Ref.set nty ((f, n) :: Ref.get nty); n
end in
let emit_app (h : int) (n : int) :=
if Int.lt n 7 then emit (Int.mul 4 (Int.add (Int.mul h 8) n)) else (emit (Int.mul 4 (Int.add (Int.mul h 8) 7)); emit n) in
let emit_limbs (l : int list) := emit (List.length l); List.iter emit l in
let rec enc (c : constr) : unit :=
let default () :=
match Unsafe.kind c with
| Unsafe.App f args =>
let k := ntypes f args in
let h := if Int.equal k 0 then f else Unsafe.make (Unsafe.App f (Array.sub args 0 k)) in
let n := Int.sub (Array.length args) k in
emit_app (head_index h) n;
Array.iter enc (Array.sub args k n)
| Unsafe.Constructor _ _ => emit_app (head_index c) 0
| Unsafe.Constant _ _ => emit_app (head_index c) 0
| Unsafe.Ind _ _ => emit_app (head_index c) 0
| Unsafe.Cast a _ t => emit 23; enc a; enc t
| _ => Control.zero (Tactic_failure (Some (Message.of_string "LD2Blob.enc: unsupported term")))
end in
let zlit (sign : int) (p : constr) :=
match nth_limbs p [] 0 0 with
| Some l => (match small_of_limbs l with
| Some v => if Int.equal sign 1 then emit (Int.add (Int.mul 4 v) 1) else (emit 3; emit v)
| None => emit 7; emit sign; emit_limbs l end)
| None => default () end in
if Constr.equal c 'Z0 then emit 1 else
if Constr.equal c 'N0 then (emit 15; emit 0) else
match Unsafe.kind c with
| Unsafe.App f args =>
if Int.equal (Array.length args) 1 then
let a := Array.get args 0 in
if Constr.equal f 'Zpos then zlit 1 a else
if Constr.equal f 'Zneg then zlit 2 a else
if Constr.equal f 'Npos then
(match nth_limbs a [] 0 0 with
| Some l => (match small_of_limbs l with Some v => emit 15; emit v | None => emit 19; emit_limbs l end)
| None => default () end) else
if Constr.equal f 'S then (match nat_val c 0 with Some n => emit (Int.add (Int.mul 4 n) 2) | None => default () end) else
if Bool.or (Constr.equal f 'xO) (Constr.equal f 'xI) then (match nth_limbs c [] 0 0 with Some l => emit 11; emit_limbs l | None => default () end) else
default ()
else default ()
| Unsafe.Constructor _ _ =>
if Constr.equal c 'O then emit 2 else
if Constr.equal c 'xH then (emit 11; emit 1; emit 1) else default ()
| _ => default ()
end in
enc c0;
Message.print (Message.of_string "LD2BLOB-BEGIN");
List.iter (fun h => Message.print (Message.concat (Message.of_string "H ") (Message.of_constr h))) (List.rev (Ref.get heads));
Message.print (List.fold_left (fun m i => Message.concat m (Message.concat (Message.of_int i) (Message.of_string ";"))) (Message.of_string "D ") (List.rev (Ref.get out)));
Message.print (Message.of_string "LD2BLOB-END").
Ltac2 encode (c0 : constr) : unit :=
Control.plus (fun () => encode_exn c0) (fun _ => Message.print (Message.of_string "LD2BLOB-FAIL")).
Ltac2 next (inp : int list Ref.ref) : int := match Ref.get inp with x :: r => Ref.set inp r; x | [] => Control.throw (Tactic_failure (Some (Message.of_string "LD2Blob: data exhausted"))) end.
Ltac2 app1 (f : constr) (a : constr) : constr := Unsafe.make (Unsafe.App f (Array.make 1 a)).
Ltac2 rec pos_of_int (v : int) : constr :=
if Int.le v 1 then 'xH else app1 (if Int.equal (Int.land v 1) 1 then 'xI else 'xO) (pos_of_int (Int.lsr v 1)).
Ltac2 pos_of_limbs (l : int list) : constr :=
let rec digits (v : int) (n : int) (hi : constr) : constr :=
if Int.equal n 0 then hi else
let d := Int.land (Int.lsr v (Int.sub n 1)) 1 in
digits v (Int.sub n 1) (app1 (if Int.equal d 1 then 'xI else 'xO) hi) in
match List.rev l with
| [] => Control.throw (Tactic_failure (Some (Message.of_string "LD2Blob: empty positive")))
| top :: rest => List.fold_left (fun hi v => digits v 30 hi) (pos_of_int top) rest
end.
Ltac2 rec read_limbs (inp : int list Ref.ref) (k : int) : int list := if Int.equal k 0 then [] else let v := next inp in v :: read_limbs inp (Int.sub k 1).
Ltac2 rec nat_of_int (n : int) (acc : constr) : constr := if Int.equal n 0 then acc else nat_of_int (Int.sub n 1) (app1 'S acc).
Ltac2 rec dec (inp : int list Ref.ref) (heads : constr array) : constr :=
let t := next inp in
let k := Int.land t 3 in let q := Int.lsr t 2 in
if Int.equal k 0 then
let h := Array.get heads (Int.lsr q 3) in
let n := Int.land q 7 in
let n := if Int.equal n 7 then next inp else n in
if Int.equal n 0 then h else
let args := Array.make n h in
let rec fill (i : int) := if Int.lt i n then (Array.set args i (dec inp heads); fill (Int.add i 1)) else () in
fill 0; Unsafe.make (Unsafe.App h args)
else if Int.equal k 1 then (if Int.equal q 0 then 'Z0 else app1 'Zpos (pos_of_int q))
else if Int.equal k 2 then nat_of_int q 'O
else
if Int.equal q 0 then app1 'Zneg (pos_of_int (next inp))
else if Int.equal q 1 then
let s := next inp in let n := next inp in let p := pos_of_limbs (read_limbs inp n) in
app1 (if Int.equal s 1 then 'Zpos else 'Zneg) p
else if Int.equal q 2 then let n := next inp in pos_of_limbs (read_limbs inp n)
else if Int.equal q 3 then let v := next inp in (if Int.equal v 0 then 'N0 else app1 'Npos (pos_of_int v))
else if Int.equal q 4 then let n := next inp in app1 'Npos (pos_of_limbs (read_limbs inp n))
else if Int.equal q 5 then let a := dec inp heads in let ty := dec inp heads in Unsafe.make (Unsafe.Cast a Constr.Cast.default ty)
else Control.throw (Tactic_failure (Some (Message.of_string "LD2Blob: bad escape"))).
Ltac2 build (heads : constr list) (data : int list) : unit :=
let inp := Ref.ref data in
let c := dec inp (Array.of_list heads) in
match Ref.get inp with
| [] => Control.refine (fun () => c)
| _ => Control.throw (Tactic_failure (Some (Message.of_string "LD2Blob: trailing data")))
end.
