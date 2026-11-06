(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
From Corelib Require Import BinNums.

Module CDef.

Ltac2 Type st := { s : string; n : int; mutable i : int; tb : string; cls : int array;
                   mutable dcache : (int * ident list) list;
                   mutable globs : constr array; mutable shr : constr array; mutable ns : int;
                   xI : constr; xO : constr; xH : constr; zpos : constr; zneg : constr; z0 : constr;
                   nS : constr; nO : constr }.

Ltac2 err (st : st) (msg : string) : 'a :=
  Control.throw (Invalid_argument (Some (Message.concat (Message.of_string "CDef: ")
     (Message.concat (Message.of_string msg) (Message.concat (Message.of_string " at offset ") (Message.of_int (st.(i)))))))).

(* [comment removed for export] *)
Ltac2 mkcls () : int array :=
  let a := Array.make 256 99 in
  let rec fill (c : int) (v : int) (k : int) := if Int.equal k 0 then () else (Array.set a c v; fill (Int.add c 1) (Int.add v 1) (Int.sub k 1)) in
  fill 48 0 10;   (* [comment removed for export] *)
  fill 97 10 6;   (* [comment removed for export] *)
  fill 103 16 16; (* [comment removed for export] *)
  a.

(* [comment removed for export] *)
Ltac2 num_at (st : st) (t : string) (o : int) : int * int :=
  let cls := st.(cls) in
  let rec go (o : int) (acc : int) :=
    let v := Array.get cls (Char.to_int (String.get t o)) in
    if Int.lt v 16 then (Int.add o 1, Int.add acc v)
    else if Int.lt v 32 then go (Int.add o 1) (Int.mul (Int.add acc (Int.sub v 16)) 16)
    else err st "number expected" in
  go o 0.

Ltac2 num (st : st) : int :=
  match num_at st (st.(s)) (st.(i)) with (o, v) => st.(i) := o; v end.

Ltac2 ident_of (st : st) (w : string) : ident :=
  match Ident.of_string w with Some id => id | None => err st "bad identifier" end.

Ltac2 name (st : st) : ident option :=
  let len := num st in
  if Int.equal len 0 then None
  else (let a := st.(i) in st.(i) := Int.add a len; Some (ident_of st (String.sub (st.(s)) a len))).

Ltac2 resolve_path (p : ident list) : constr :=
  match Env.get p with
  | Some r => Env.instantiate r
  | None => Control.throw (Invalid_argument (Some (Message.of_string "CDef: unknown builtin global")))
  end.

Ltac2 binder (na : ident option) (ty : constr) : binder :=
  Constr.Binder.unsafe_make na Constr.Binder.Relevant ty.

Ltac2 mk (k : Constr.Unsafe.kind) : constr := Constr.Unsafe.make k.

(* [comment removed for export] *)
Ltac2 positive (st : st) : constr :=
  let cls := st.(cls) in let s := st.(s) in
  let xI := st.(xI) in let xO := st.(xO) in
  let bit (w : int) (acc : constr option) :=
    match acc with
    | None => if Int.equal w 0 then None else Some (st.(xH))
    | Some c => Some (mk (Constr.Unsafe.App (if Int.equal w 0 then xO else xI) [| c |]))
    end in
  let rec go (o : int) (acc : constr option) :=
    let v := Array.get cls (Char.to_int (String.get s o)) in
    let d := if Int.lt v 16 then v else if Int.lt v 32 then Int.sub v 16 else err st "digit expected" in
    let acc := bit (Int.land d 8) acc in
    let acc := bit (Int.land d 4) acc in
    let acc := bit (Int.land d 2) acc in
    let acc := bit (Int.land d 1) acc in
    if Int.lt v 16 then (st.(i) := Int.add o 1; acc) else go (Int.add o 1) acc in
  match go (st.(i)) None with Some c => c | None => err st "zero positive literal" end.

Ltac2 natlit (st : st) (k : int) : constr :=
  let sc := st.(nS) in
  let rec go (k : int) (acc : constr) := if Int.equal k 0 then acc else go (Int.sub k 1) (mk (Constr.Unsafe.App sc [| acc |])) in
  go k (st.(nO)).

Ltac2 ind_of (st : st) (c : constr) : inductive :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Ind ind _ => ind
  | _ => err st "inductive expected"
  end.

Ltac2 sort_of (st : st) (c : constr) : constr :=
  match Constr.Unsafe.kind c with Constr.Unsafe.Sort _ => c | _ => err st "sort" end.

Ltac2 rec term (st : st) : constr :=
  let k := st.(i) in
  st.(i) := Int.add k 1;
  let c := Char.to_int (String.get (st.(s)) k) in
  (* [comment removed for export] *)
  if Int.equal c 36 (* [comment removed for export] *) then Array.get (st.(globs)) (num st)
  else if Int.equal c 94 (* [comment removed for export] *) then mk (Constr.Unsafe.Rel (num st))
  else if Int.equal c 64 (* [comment removed for export] *) then
    (let n := num st in
     let f := term st in
     let args := Array.make n f in
     let rec fill (j : int) := if Int.equal j n then () else (Array.set args j (term st); fill (Int.add j 1)) in
     fill 0; mk (Constr.Unsafe.App f args))
  else if Int.lt c 65 then
    (if Int.equal c 62 (* [comment removed for export] *) then
       (let na := name st in let ty := term st in let body := term st in mk (Constr.Unsafe.Prod (binder na ty) body))
     else if Int.equal c 43 (* [comment removed for export] *) then mk (Constr.Unsafe.App (st.(zpos)) [| positive st |])
     else if Int.equal c 61 (* [comment removed for export] *) then
       (let na := name st in let ty := term st in let v := term st in let body := term st in
        mk (Constr.Unsafe.LetIn (binder na ty) v body))
     else if Int.equal c 63 (* [comment removed for export] *) then (match name st with Some id => mk (Constr.Unsafe.Var id) | None => err st "variable name expected" end)
     else if Int.equal c 35 (* [comment removed for export] *) then positive st
     else if Int.equal c 45 (* [comment removed for export] *) then mk (Constr.Unsafe.App (st.(zneg)) [| positive st |])
     else err st "unknown tag")
  else if Int.equal c 126 (* [comment removed for export] *) then
    (let j := num st in if Int.lt j (st.(ns)) then Array.get (st.(shr)) j else err st "shared index out of range")
  else if Int.equal c 92 (* [comment removed for export] *) then
    (let na := name st in let ty := term st in let body := term st in mk (Constr.Unsafe.Lambda (binder na ty) body))
  else if Int.equal c 80 (* [comment removed for export] *) then sort_of st 'Prop
  else if Int.equal c 90 (* [comment removed for export] *) then st.(z0)
  else if Int.equal c 83 (* [comment removed for export] *) then sort_of st 'Set
  else if Int.equal c 84 (* [comment removed for export] *) then sort_of st 'Type
  else if Int.equal c 78 (* [comment removed for export] *) then natlit st (num st)
  else if Int.equal c 77 (* [comment removed for export] *) then
    (let indc := Array.get (st.(globs)) (num st) in
     let ind := ind_of st indc in
     let ci := Constr.Unsafe.case ind in
     let nbr := Ind.nconstructors (Ind.data ind) in
     let ret := term st in
     let scr := term st in
     let brs := Array.make nbr scr in
     let rec fill (j : int) := if Int.equal j nbr then () else (Array.set brs j (term st); fill (Int.add j 1)) in
     fill 0;
     mk (Constr.Unsafe.Case ci (ret, Constr.Binder.Relevant) Constr.Unsafe.NoInvert scr brs))
  else if Int.equal c 88 (* [comment removed for export] *) then
    (let cnt := num st in
     let sel := num st in
     let structs := Array.make cnt 0 in
     let bnds := Array.make cnt (binder None (st.(nO))) in
     let rec fillb (j : int) :=
       if Int.equal j cnt then ()
       else (let si := num st in let na := name st in let ty := term st in
             Array.set structs j si; Array.set bnds j (binder na ty); fillb (Int.add j 1)) in
     fillb 0;
     let bodies := Array.make cnt (st.(nO)) in
     let rec fillc (j : int) := if Int.equal j cnt then () else (Array.set bodies j (term st); fillc (Int.add j 1)) in
     fillc 0;
     mk (Constr.Unsafe.Fix structs sel bnds bodies))
  else if Int.equal c 75 (* [comment removed for export] *) then
    (let q := st.(i) in
     st.(i) := Int.add q 1;
     let kc := Char.to_int (String.get (st.(s)) q) in
     let ck := if Int.equal kc 100 then Constr.Cast.default else if Int.equal kc 118 then Constr.Cast.vm
               else if Int.equal kc 110 then Constr.Cast.native else err st "cast kind" in
     let v := term st in let ty := term st in mk (Constr.Unsafe.Cast v ck ty))
  else if Int.equal c 73 (* [comment removed for export] *) then mk (Constr.Unsafe.Uint63 (Uint63.of_int (num st)))
  else if Int.equal c 74 (* [comment removed for export] *) then
    (let indc := Array.get (st.(globs)) (num st) in
     let pi := num st in
     let unf := num st in
     let ind := ind_of st indc in
     let ps := match Ind.get_projections (Ind.data ind) with Some ps => ps | None => err st "record without primitive projections" end in
     let p := Proj.set_unfolded (Array.get ps pi) (Int.equal unf 1) in
     let r := term st in
     mk (Constr.Unsafe.Proj p Constr.Binder.Relevant r))
  else err st "unknown tag".

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 dir_at (st : st) (o : int) : ident list :=
  match List.find_opt (fun p => match p with (k, _) => Int.equal k o end) (st.(dcache)) with
  | Some p => (match p with (_, d) => d end)
  | None =>
    let t := st.(tb) in
    let rec pieces (o : int) (k : int) (acc : string list) :=
      if Int.equal k 0 then (o, String.concat "" (List.rev acc))
      else match num_at st t o with (o3, len) => pieces (Int.add o3 len) (Int.sub k 1) (String.sub t o3 len :: acc) end in
    let rec go (o : int) (k : int) (acc : ident list) :=
      if Int.equal k 0 then List.rev acc
      else match num_at st t o with (o2, len) =>
             if Int.equal len 0 then
               (match num_at st t o2 with (o3, np) =>
                match pieces o3 np [] with (o4, w) => go o4 (Int.sub k 1) (ident_of st w :: acc) end end)
             else go (Int.add o2 len) (Int.sub k 1) (ident_of st (String.sub t o2 len) :: acc) end in
    let d := match num_at st t o with (o1, ncomp) => go o1 ncomp [] end in
    st.(dcache) := (o, d) :: st.(dcache); d
  end.

(* [comment removed for export] *)
Ltac2 glob_at (st : st) (o : int) : constr :=
  let t := st.(tb) in
  match num_at st t o with (o1, diroff) =>
    let nm :=
      if Int.equal (Char.to_int (String.get t o1)) 124
      then match num_at st t (Int.add o1 1) with (o2, np) =>
             let rec pieces (o : int) (k : int) (acc : string list) :=
               if Int.equal k 0 then String.concat "" (List.rev acc)
               else match num_at st t o with (o3, len) => pieces (Int.add o3 len) (Int.sub k 1) (String.sub t o3 len :: acc) end in
             ident_of st (pieces o2 np []) end
      else match num_at st t o1 with (o2, len) => ident_of st (String.sub t o2 len) end in
    let p := List.append (dir_at st diroff) [nm] in
    match Env.get p with
    | Some r => Env.instantiate r
    | None => err st (String.app "unknown global " (String.concat "." (List.map Ident.to_string p)))
    end
  end.

Ltac2 header (st : st) : unit :=
  let cg := num st in
  let cs := num st in
  st.(globs) := Array.make cg (st.(nO));
  st.(shr) := Array.make cs (st.(nO)); st.(ns) := 0;
  let s := st.(s) in
  let rec gl (j : int) :=
    if Int.equal j cg then ()
    else (let q := st.(i) in
          (if Int.equal (Char.to_int (String.get s q)) 33 (* [comment removed for export] *) then st.(i) := Int.add q 1 else err st "'!' expected");
          Array.set (st.(globs)) j (glob_at st (num st)); gl (Int.add j 1)) in
  gl 0;
  let rec sh (j : int) :=
    if Int.equal j cs then ()
    else (let q := st.(i) in
          (if Int.equal (Char.to_int (String.get s q)) 38 (* [comment removed for export] *) then st.(i) := Int.add q 1 else err st "'&' expected");
          let t := term st in Array.set (st.(shr)) j t; st.(ns) := Int.add j 1; sh (Int.add j 1)) in
  sh 0.

Ltac2 decode (tbl : string) (s : string) : constr :=
  let gp (p : ident list) := resolve_path p in
  let st := { s := s; n := String.length s; i := 0; tb := tbl; cls := mkcls (); dcache := [];
              globs := Array.empty; shr := Array.empty; ns := 0;
              xI := gp [@Corelib; @Numbers; @BinNums; @xI]; xO := gp [@Corelib; @Numbers; @BinNums; @xO]; xH := gp [@Corelib; @Numbers; @BinNums; @xH];
              zpos := gp [@Corelib; @Numbers; @BinNums; @Zpos]; zneg := gp [@Corelib; @Numbers; @BinNums; @Zneg];
              z0 := gp [@Corelib; @Numbers; @BinNums; @Z0];
              nS := gp [@Corelib; @Init; @Datatypes; @S]; nO := gp [@Corelib; @Init; @Datatypes; @O] } in
  header st;
  let t := term st in
  if Int.equal (st.(i)) (st.(n)) then t else err st "trailing characters".

(* [comment removed for export] *)
Ltac2 cdeft (tbl : string) (s : string) : unit := let t := decode tbl s in Control.refine (fun () => t).

End CDef.
