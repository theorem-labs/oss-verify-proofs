(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Corelib Require BinNums.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr.
Import Constr.Unsafe.

Module RP.
Ltac2 Type st := { str : string; mutable pos : int; tab : constr array; gl : string array; gc : constr option array; sty : bool ref }.

Ltac2 getc (r : st) : int := let c := Char.to_int (String.get (r.(str)) (r.(pos))) in r.(pos) := Int.add (r.(pos)) 1; c.

Ltac2 rec rnum_acc (r : st) (acc : int) : int :=
  let c := getc r in if Int.equal c 59 then acc else rnum_acc r (Int.add (Int.mul acc 10) (Int.sub c 48)).
Ltac2 rnum (r : st) : int := rnum_acc r 0.

Ltac2 rec scan_to_semi (r : st) : unit := if Int.equal (getc r) 59 then () else scan_to_semi r.
Ltac2 rid (r : st) : ident :=
  let p0 := r.(pos) in scan_to_semi r;
  match Ident.of_string (String.sub (r.(str)) p0 (Int.sub (Int.sub (r.(pos)) p0) 1)) with
  | Some i => i | None => Control.throw (Tactic_failure (Some (Message.of_string "Rpl: bad ident")))
  end.

Ltac2 rname (r : st) : ident option :=
  if Int.equal (Char.to_int (String.get (r.(str)) (r.(pos)))) 126 then (let _ := getc r in None) else Some (rid r).

Ltac2 rrel (r : st) : Binder.relevance :=
  let c := getc r in if Int.equal c 82 then Binder.Relevant else Binder.Irrelevant.

(* [comment removed for export] *)
Ltac2 rec split_path (s : string) (i : int) (j : int) (acc : ident list) : ident list :=
  if Int.equal j (String.length s) then
    (match Ident.of_string (String.sub s i (Int.sub j i)) with Some id => List.rev (id :: acc) | None => Control.throw Not_found end)
  else if Int.equal (Char.to_int (String.get s j)) 46 then
    (match Ident.of_string (String.sub s i (Int.sub j i)) with Some id => split_path s (Int.add j 1) (Int.add j 1) (id :: acc) | None => Control.throw Not_found end)
  else split_path s i (Int.add j 1) acc.

Ltac2 glob (r : st) (g : int) : constr :=
  match Array.get (r.(gc)) g with
  | Some c => c
  | None =>
    let p := Array.get (r.(gl)) g in
    let c := match Env.get (split_path p 0 0 []) with
             | Some rf => Env.instantiate rf
             | None => Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "Rpl: unknown global ") (Message.of_string p))))
             end in
    Array.set (r.(gc)) g (Some c); c
  end.

Ltac2 ind_of (c : constr) : inductive :=
  match kind c with Ind i _ => i | _ => Control.throw (Tactic_failure (Some (Message.of_string "Rpl: not an inductive"))) end.

Ltac2 rec rterm (r : st) : constr :=
  let c := getc r in
  if Int.equal c 65 (* [comment removed for export] *) then
    let n := rnum r in let f := rterm r in
    let a := Array.make n f in
    let rec fill i := if Int.equal i n then () else (Array.set a i (rterm r); fill (Int.add i 1)) in
    fill 0; make (App f a)
  else if Int.equal c 114 (* [comment removed for export] *) then make (Rel (rnum r))
  else if Int.equal c 35 (* [comment removed for export] *) then Array.get (r.(tab)) (rnum r)
  else if Int.equal c 107 (* [comment removed for export] *) then glob r (rnum r)
  else if Int.equal c 111 (* [comment removed for export] *) then glob r (rnum r)
  else if Int.equal c 105 (* [comment removed for export] *) then glob r (rnum r)
  else if Int.equal c 76 (* [comment removed for export] *) then
    let na := rname r in let rl := rrel r in let ty := rterm r in let bd := rterm r in
    make (Lambda (Binder.unsafe_make na rl ty) bd)
  else if Int.equal c 80 (* [comment removed for export] *) then
    let na := rname r in let rl := rrel r in let ty := rterm r in let bd := rterm r in
    make (Prod (Binder.unsafe_make na rl ty) bd)
  else if Int.equal c 69 (* [comment removed for export] *) then
    let na := rname r in let rl := rrel r in let v := rterm r in let ty := rterm r in let bd := rterm r in
    make (LetIn (Binder.unsafe_make na rl ty) v bd)
  else if Int.equal c 118 (* [comment removed for export] *) then make (Var (rid r))
  else if Int.equal c 99 (* [comment removed for export] *) then
    let k := getc r in let t := rterm r in let ty := rterm r in
    match kind (if Int.equal k 118 then '(I <: True) else if Int.equal k 110 then '(I <<: True) else '(I : True)) with
    | Cast _ ck _ => make (Cast t ck ty)
    | _ => Control.throw Not_found
    end
  else if Int.equal c 109 (* [comment removed for export] *) then
    let g := rnum r in let ind := ind_of (glob r g) in let rl := rrel r in
    let iv := (let t := getc r in
               if Int.equal t 78 then NoInvert
               else (let n := rnum r in let a := Array.make n '(I) in
                     let rec fill i := if Int.equal i n then () else (Array.set a i (rterm r); fill (Int.add i 1)) in
                     fill 0; CaseInvert a)) in
    let ret := rterm r in let sc := rterm r in
    let n := rnum r in let a := Array.make n '(I) in
    let rec fill i := if Int.equal i n then () else (Array.set a i (rterm r); fill (Int.add i 1)) in
    fill 0;
    make (Case (case ind) (ret, (if Int.equal 0 0 then rl else rl)) iv sc a)
  else if Int.equal c 102 (* [comment removed for export] *) then
    let n := rnum r in let i := rnum r in
    let ria := Array.make n 0 in
    let rec fr j := if Int.equal j n then () else (Array.set ria j (rnum r); fr (Int.add j 1)) in fr 0;
    let nas := Array.make n (None, Binder.Relevant) in
    let rec fn j := if Int.equal j n then () else (let na := rname r in let rl := rrel r in Array.set nas j (na, rl); fn (Int.add j 1)) in fn 0;
    let tys := Array.make n '(I) in
    let rec ft j := if Int.equal j n then () else (Array.set tys j (rterm r); ft (Int.add j 1)) in ft 0;
    let bds := Array.make n '(I) in
    let rec fb j := if Int.equal j n then () else (Array.set bds j (rterm r); fb (Int.add j 1)) in fb 0;
    let bs := Array.make n (Binder.unsafe_make None Binder.Relevant '(I)) in
    let rec fbs j := if Int.equal j n then () else (let (na, rl) := Array.get nas j in Array.set bs j (Binder.unsafe_make na rl (Array.get tys j)); fbs (Int.add j 1)) in fbs 0;
    make (Fix ria i bs bds)
  else if Int.equal c 112 (* [comment removed for export] *) then 'Prop
  else if Int.equal c 115 (* [comment removed for export] *) then 'Set
  else if Int.equal c 113 (* [comment removed for export] *) then 'SProp
  else if Int.equal c 116 (* [comment removed for export] *) then (r.(sty).(contents) := true; 'Type)
  else if Int.equal c 110 (* [comment removed for export] *) then
    make (Uint63 (Uint63.of_int (rnum r)))
  else if Int.equal c 78 (* [comment removed for export] *) then
    let n := rnum r in
    let sc := '(@Corelib.Init.Datatypes.S) in
    let rec mk i acc := if Int.equal i 0 then acc else mk (Int.sub i 1) (make (App sc [| acc |])) in
    mk n '(@Corelib.Init.Datatypes.O)
  else if Int.equal c 89 (* [comment removed for export] *) then
    let k := rnum r in
    let nd := Int.div (Int.add k 3) 4 in
    let xi := '(@Corelib.Numbers.BinNums.xI) in
    let xo := '(@Corelib.Numbers.BinNums.xO) in
    let rec digits i skip p :=
      if Int.equal i nd then p else
      let ch := getc r in
      let v := if Int.le ch 57 then Int.sub ch 48 else Int.sub ch 87 in
      let rec bits j skip p :=
        if Int.lt j 0 then (skip, p)
        else if Int.gt skip 0 then bits (Int.sub j 1) (Int.sub skip 1) p
        else bits (Int.sub j 1) 0 (make (App (if Int.equal (Int.land (Int.lsr v j) 1) 1 then xi else xo) [| p |])) in
      let (skip', p') := bits 3 skip p in digits (Int.add i 1) skip' p' in
    let p := digits 0 (Int.sub (Int.mul nd 4) k) '(@Corelib.Numbers.BinNums.xH) in
    let _ := getc r in p
  else Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "Rpl: bad tag at ") (Message.of_int (r.(pos)))))).

Ltac2 decode (sty : bool ref) (gl : string array) (s : string) : constr :=
  let r0 := { str := s; pos := 0; tab := Array.empty; gl := gl; gc := Array.make (Array.length gl) None; sty := sty } in
  let h := getc r0 in   (* [comment removed for export] *)
  (if Int.equal h 85 then sty.(contents) := true else ());
  let n := rnum r0 in
  let tab := Array.make n '(I) in
  let r := { str := s; pos := r0.(pos); tab := tab; gl := gl; gc := r0.(gc); sty := sty } in
  let rec fill i := if Int.equal i n then () else (Array.set tab i (rterm r); fill (Int.add i 1)) in
  fill 0; rterm r.

(* [comment removed for export] *)
Ltac2 rec lastk (l : (ident * constr option * constr) list) (k : int) : ident list :=
  let n := List.length l in
  if Int.le n k then List.map (fun (h : ident * constr option * constr) => let (i, _, _) := h in i) l
  else match l with _ :: t => lastk t k | [] => [] end.

(* [comment removed for export] *)
Ltac2 rec peel (t : constr) (k : int) : constr :=
  if Int.equal k 0 then t else
  match kind t with
  | Lambda _ b => peel b (Int.sub k 1)
  | _ => Control.throw (Tactic_failure (Some (Message.of_string "Rpl: fewer lambdas than statement binders")))
  end.

(* [comment removed for export] *)
Ltac2 run_k (gl : string array) (k : int) (s : string) : unit :=
  let sty := { contents := false } in
  let t0 := decode sty gl s in
  let t := (if Int.equal k 0 then t0 else
             let hs := lastk (Control.hyps ()) k in
             substnl (List.rev (List.map (fun i => make (Var i)) hs)) 0 (peel t0 k)) in
  if sty.(contents) then Control.refine (fun () => t)
  else Std.exact_no_check t.
Ltac2 run (gl : string array) (s : string) : unit := run_k gl 0 s.
End RP.
