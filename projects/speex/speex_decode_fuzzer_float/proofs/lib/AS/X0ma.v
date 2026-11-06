(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Ltac2 Require Ltac2.

Module CTermR.
Import Ltac2.Ltac2.

Ltac2 Type st := { str : string; len : int; mutable pos : int; glob : constr array;
cxH : constr; cxO : constr; cxI : constr; cZ0 : constr; cZpos : constr; cZneg : constr;
cO : constr; cS : constr; ccons : constr; cnil : constr }.

Ltac2 bad (m : string) := Control.throw (Tactic_failure (Some (Message.of_string (String.app "CTerm: " m)))).

Ltac2 rec split_from (s : string) (i : int) (j : int) (acc : string list) : string list :=
if Int.equal j (String.length s) then List.rev (String.sub s i (Int.sub j i) :: acc)
else if Int.equal (Char.to_int (String.get s j)) 46 then split_from s (Int.add j 1) (Int.add j 1) (String.sub s i (Int.sub j i) :: acc)
else split_from s i (Int.add j 1) acc.

Ltac2 gref (path : string) : constr :=
let ids := List.map (fun x => match Ident.of_string x with Some i => i | None => bad (String.app "bad ident in " path) end) (split_from path 0 0 []) in
match Env.get ids with
| Some r => Env.instantiate r
| None => match Env.expand ids with r :: _ => Env.instantiate r | [] => bad (String.app "unknown global " path) end
end.

Ltac2 app (h : constr) (args : constr array) : constr := Constr.Unsafe.make (Constr.Unsafe.App h args).

Ltac2 peek (st : st) : int :=
if Int.lt (st.(pos)) (st.(len)) then Char.to_int (String.get (st.(str)) (st.(pos))) else 0.
Ltac2 adv (st : st) : unit := st.(pos) := Int.add (st.(pos)) 1.

Ltac2 dval (c : int) : int :=
if Int.le 48 c then (if Int.le c 57 then Int.sub c 48 else if Int.le 97 c then (if Int.le c 118 then Int.sub c 87 else Int.neg 1) else Int.neg 1)
else Int.neg 1.

Ltac2 rec rdnum_aux (st : st) (acc : int) : int :=
let d := dval (peek st) in
if Int.ge d 0 then (adv st; rdnum_aux st (Int.add (Int.mul acc 32) d)) else acc.
Ltac2 rdnum (st : st) : int :=
if Int.ge (dval (peek st)) 0 then rdnum_aux st 0 else bad "number expected".

Ltac2 rec pos_bits (st : st) (p : constr option) (d : int) (k : int) : constr option :=
if Int.lt k 0 then p
else
let b := Int.land (Int.lsr d k) 1 in
let p2 := match p with
| None => if Int.equal b 1 then Some (st.(cxH)) else None
| Some q => Some (app (if Int.equal b 1 then st.(cxI) else st.(cxO)) [| q |])
end in
pos_bits st p2 d (Int.sub k 1).
Ltac2 rec rdpos_aux (st : st) (p : constr option) : constr option :=
let d := dval (peek st) in
if Int.ge d 0 then (adv st; rdpos_aux st (pos_bits st p d 4)) else p.
Ltac2 rdpos (st : st) : constr :=
match rdpos_aux st None with Some p => p | None => bad "positive literal 0" end.

Ltac2 rec nat_of (st : st) (n : int) (acc : constr) : constr :=
if Int.equal n 0 then acc else nat_of st (Int.sub n 1) (app (st.(cS)) [| acc |]).

Ltac2 rec rd (st : st) : constr :=
let c := peek st in
adv st;
if Int.equal c 65 then
let n := rdnum st in
let h := rd st in
let args := Array.make n h in
rd_into st args 0 n;
app h args
else if Int.equal c 71 then
let k := rdnum st in
if Int.lt k (Array.length (st.(glob))) then Array.get (st.(glob)) k else bad "global index"
else if Int.equal c 80 then rdpos st
else if Int.equal c 81 then app (st.(cZpos)) [| rdpos st |]
else if Int.equal c 77 then app (st.(cZneg)) [| rdpos st |]
else if Int.equal c 79 then st.(cZ0)
else if Int.equal c 78 then nat_of st (rdnum st) (st.(cO))
else if Int.equal c 76 then
let n := rdnum st in
let t := rd st in
let es := Array.make n t in
rd_into st es 0 n;
mk_list st t es 0 n (app (st.(cnil)) [| t |])
else bad "unknown tag"

with rd_into (st : st) (a : constr array) (i : int) (n : int) : unit :=
if Int.le (Int.sub n i) 8 then rd_seq st a i n
else let m := Int.add i (Int.div (Int.sub n i) 2) in (rd_into st a i m; rd_into st a m n)
with rd_seq (st : st) (a : constr array) (i : int) (n : int) : unit :=
if Int.lt i n then (Array.set a i (rd st); rd_seq st a (Int.add i 1) n) else ()

with mk_list (st : st) (t : constr) (es : constr array) (i : int) (j : int) (tl : constr) : constr :=
if Int.le (Int.sub j i) 8 then mk_seq st t es i (Int.sub j 1) tl
else let m := Int.add i (Int.div (Int.sub j i) 2) in mk_list st t es i m (mk_list st t es m j tl)
with mk_seq (st : st) (t : constr) (es : constr array) (i : int) (k : int) (acc : constr) : constr :=
if Int.lt k i then acc else mk_seq st t es i (Int.sub k 1) (app (st.(ccons)) [| t; Array.get es k; acc |]).

Ltac2 read (tbl : string list) (s : string) : constr :=
let st := { str := s; len := String.length s; pos := 0; glob := Array.of_list (List.map gref tbl);
cxH := gref "Corelib.Numbers.BinNums.xH"; cxO := gref "Corelib.Numbers.BinNums.xO"; cxI := gref "Corelib.Numbers.BinNums.xI";
cZ0 := gref "Corelib.Numbers.BinNums.Z0"; cZpos := gref "Corelib.Numbers.BinNums.Zpos"; cZneg := gref "Corelib.Numbers.BinNums.Zneg";
cO := gref "Corelib.Init.Datatypes.O"; cS := gref "Corelib.Init.Datatypes.S";
ccons := gref "Corelib.Init.Datatypes.cons"; cnil := gref "Corelib.Init.Datatypes.nil" } in
let t := rd st in
if Int.equal (st.(pos)) (st.(len)) then t else bad "trailing characters".

Ltac2 make (tbl : string list) (s : string) : unit := Std.exact_no_check (read tbl s).

End CTermR.
