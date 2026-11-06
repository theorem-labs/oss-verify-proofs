(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Corelib Require BinNums.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Constr.
From Ltac2 Require Unification TransparentState.
Import Constr.Unsafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RP.
Ltac2 Type st := { str : string; mutable pos : int; tab : constr array; gl : int -> Std.reference option; gc : constr option array; sty : bool ref; filler : constr;
                   hypt : constr list; concl : constr; kc : constr option array }.
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac2 fail (m : string) : 'a := Control.throw (Tactic_failure (Some (Message.of_string m))).

Ltac2 gref (p : ident list) : constr :=
  match Env.get p with Some r => Env.instantiate r | None => Control.throw Not_found end.
Ltac2 kval (i : int) : constr :=
  if Int.equal i 0 then 'Prop else if Int.equal i 1 then 'Set else if Int.equal i 2 then 'SProp
  else if Int.equal i 3 then gref [@Corelib; @Init; @Datatypes; @S] else if Int.equal i 4 then gref [@Corelib; @Init; @Datatypes; @O]
  else if Int.equal i 5 then gref [@Corelib; @Numbers; @BinNums; @xI] else if Int.equal i 6 then gref [@Corelib; @Numbers; @BinNums; @xO]
  else if Int.equal i 7 then gref [@Corelib; @Numbers; @BinNums; @xH]
  else if Int.equal i 8 then '(I <: True) else if Int.equal i 9 then '(I <<: True) else '(I : True).

Ltac2 konst (r : st) (i : int) : constr :=
  match Array.get (r.(kc)) i with
  | Some c => c
  | None => let c := kval i in Array.set (r.(kc)) i (Some c); c
  end.

Ltac2 getc (r : st) : int := let p := r.(pos) in r.(pos) := Int.add p 1; Char.to_int (String.get (r.(str)) p).
Ltac2 peekc (r : st) : int := Char.to_int (String.get (r.(str)) (r.(pos))).

(* [comment removed for export] *)
Ltac2 rec rnum_c (r : st) (acc : int) : int :=
  let c := getc r in
  if Int.equal (Int.compare c 93) -1 then Int.add (Int.mul acc 45) (Int.sub c 48) else rnum_c r (Int.add (Int.mul acc 25) (Int.sub c 93)).
Ltac2 rnum (r : st) : int :=
  let c := getc r in
  if Int.equal (Int.compare c 93) -1 then Int.sub c 48 else rnum_c r (Int.sub c 93).

(* [comment removed for export] *)
Ltac2 rec rdec_acc (r : st) (acc : int) : int :=
  let c := getc r in if Int.equal c 59 then acc else rdec_acc r (Int.add (Int.mul acc 10) (Int.sub c 48)).

Ltac2 rec scan_to_semi (r : st) : unit := if Int.equal (getc r) 59 then () else scan_to_semi r.
Ltac2 rid (r : st) : ident :=
  let p0 := r.(pos) in scan_to_semi r;
  match Ident.of_string (String.sub (r.(str)) p0 (Int.sub (Int.sub (r.(pos)) p0) 1)) with
  | Some i => i | None => fail "Rpl: bad ident"
  end.
Ltac2 rname (r : st) : ident option := if Int.equal (peekc r) 126 then (r.(pos) := Int.add (r.(pos)) 1; None) else Some (rid r).
Ltac2 rrel (r : st) : Binder.relevance := if Int.equal (getc r) 82 then Binder.Relevant else Binder.Irrelevant.

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
    let c := match (r.(gl)) g with
             | Some rf => Env.instantiate rf
             | None => Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "Rpl: unknown global #") (Message.of_int g))))
             end in
    Array.set (r.(gc)) g (Some c); c
  end.

Ltac2 ind_of (c : constr) : inductive := match kind c with Ind i _ => i | _ => fail "Rpl: not an inductive" end.

(* [comment removed for export] *)
Ltac2 rec nav (r : st) (t : constr) : constr :=
  let c := getc r in
  if Int.equal c 59 then t
  else if Int.equal c 100 (* [comment removed for export] *) then (match kind t with Prod b _ => nav r (Binder.type b) | Lambda b _ => nav r (Binder.type b) | _ => fail "Rpl: nav d" end)
  else if Int.equal c 98 (* [comment removed for export] *) then (match kind t with Prod _ k => nav r k | Lambda _ k => nav r k | _ => fail "Rpl: nav b" end)
  else if Int.equal c 104 (* [comment removed for export] *) then (match kind t with App f _ => nav r f | _ => fail "Rpl: nav h" end)
  else if Int.equal c 97 (* [comment removed for export] *) then (let i := rnum r in match kind t with App _ a => nav r (Array.get a i) | _ => fail "Rpl: nav a" end)
  else if Int.equal c 101 (* [comment removed for export] *) then (match kind t with Cast k _ _ => nav r k | _ => fail "Rpl: nav e" end)
  else if Int.equal c 86 (* [comment removed for export] *) then (match kind t with LetIn _ v _ => nav r v | _ => fail "Rpl: nav V" end)
  else if Int.equal c 84 (* [comment removed for export] *) then (match kind t with LetIn b _ _ => nav r (Binder.type b) | _ => fail "Rpl: nav T" end)
  else fail "Rpl: nav step".
Ltac2 rec navs (r : st) (hyps : constr list) (concl : constr) : constr :=
  match hyps with
  | [] => nav r concl
  | ty :: rest =>
    let c := getc r in
    if Int.equal c 100 (* [comment removed for export] *) then nav r ty
    else if Int.equal c 98 (* [comment removed for export] *) then navs r rest concl
    else fail "Rpl: nav statement"
  end.
Ltac2 rlev (r : st) : constr :=
  let c := getc r in
  if Int.equal c 115 (* [comment removed for export] *) then konst r 1
  else if Int.equal c 103 (* [comment removed for export] *) then (let g := rnum r in nav r (Constr.type (glob r g)))
  else if Int.equal c 99 (* [comment removed for export] *) then navs r (r.(hypt)) (r.(concl))
  else fail "Rpl: lev".

Ltac2 rec fill (r : st) (a : constr array) (i : int) (n : int) (f : st -> constr) : unit :=
  if Int.equal i n then () else (Array.set a i (f r); fill r a (Int.add i 1) n f).

Ltac2 rec rterm (r : st) : constr :=
  let c := getc r in
  if Int.equal (Int.compare c 48) -1 then low r c
  else if Int.equal (Int.compare c 93) -1 then Array.get (r.(tab)) (Int.sub c 48)
  else if Int.equal (Int.compare c 118) -1 then Array.get (r.(tab)) (rnum_c r (Int.sub c 93))
  else high r c
with low (r : st) (c : int) : constr :=
  if Int.equal c 33 (* [comment removed for export] *) then
    (let n := rnum r in let f := rterm r in let a := Array.make n f in fill r a 0 n rterm; make (App f a))
  else if Int.equal c 35 (* [comment removed for export] *) then make (Rel (rnum r))
  else if Int.equal c 39 (* [comment removed for export] *) then glob r (rnum r)
  else if Int.equal c 43 (* [comment removed for export] *) then glob r (rnum r)
  else if Int.equal c 38 (* [comment removed for export] *) then
    (let na := rname r in let rl := rrel r in let v := rterm r in let ty := rterm r in let bd := rterm r in make (LetIn (Binder.unsafe_make na rl ty) v bd))
  else if Int.equal c 44 (* [comment removed for export] *) then glob r (rnum r)
  else if Int.equal c 37 (* [comment removed for export] *) then
    (let na := rname r in let rl := rrel r in let ty := rterm r in let bd := rterm r in make (Prod (Binder.unsafe_make na rl ty) bd))
  else if Int.equal c 36 (* [comment removed for export] *) then
    (let na := rname r in let rl := rrel r in let ty := rterm r in let bd := rterm r in make (Lambda (Binder.unsafe_make na rl ty) bd))
  else if Int.equal c 45 (* [comment removed for export] *) then
    (let g := rnum r in let ind := ind_of (glob r g) in let rl := rrel r in
     let iv := (let t := getc r in
                if Int.equal t 78 then NoInvert
                else (let n := rnum r in let a := Array.make n (r.(filler)) in fill r a 0 n rterm; CaseInvert a)) in
     let ret := rterm r in let sc := rterm r in
     let n := rnum r in let a := Array.make n (r.(filler)) in fill r a 0 n rterm;
     make (Case (case ind) (ret, rl) iv sc a))
  else if Int.equal c 46 (* [comment removed for export] *) then
    (let n := rnum r in let i := rnum r in
     let ria := Array.make n 0 in
     let rec fr j := if Int.equal j n then () else (Array.set ria j (rnum r); fr (Int.add j 1)) in fr 0;
     let nas := Array.make n (None, Binder.Relevant) in
     let rec fn j := if Int.equal j n then () else (let na := rname r in let rl := rrel r in Array.set nas j (na, rl); fn (Int.add j 1)) in fn 0;
     let tys := Array.make n (r.(filler)) in fill r tys 0 n rterm;
     let bds := Array.make n (r.(filler)) in fill r bds 0 n rterm;
     let bs := Array.make n (Binder.unsafe_make None Binder.Relevant (r.(filler))) in
     let rec fbs j := if Int.equal j n then () else (let (na, rl) := Array.get nas j in Array.set bs j (Binder.unsafe_make na rl (Array.get tys j)); fbs (Int.add j 1)) in fbs 0;
     make (Fix ria i bs bds))
  else if Int.equal c 47 (* [comment removed for export] *) then make (Var (rid r))
  else Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "Rpl: bad low tag at ") (Message.of_int (r.(pos))))))
with high (r : st) (c : int) : constr :=
  if Int.equal c 118 (* [comment removed for export] *) then
    (let k := getc r in let t := rterm r in let ty := rterm r in
     match kind (konst r (if Int.equal k 118 then 8 else if Int.equal k 110 then 9 else 10)) with
     | Cast _ ck _ => make (Cast t ck ty)
     | _ => Control.throw Not_found
     end)
  else if Int.equal c 119 (* [comment removed for export] *) then konst r 0
  else if Int.equal c 120 (* [comment removed for export] *) then konst r 1
  else if Int.equal c 121 (* [comment removed for export] *) then konst r 2
  else if Int.equal c 122 (* [comment removed for export] *) then (r.(sty).(contents) := true; 'Type)
  else if Int.equal c 123 (* [comment removed for export] *) then rlev r
  else if Int.equal c 125 (* [comment removed for export] *) then
    (let n := rnum r in
     let sc := konst r 3 in
     let rec mk i acc := if Int.equal i 0 then acc else mk (Int.sub i 1) (make (App sc [| acc |])) in
     mk n (konst r 4))
  else if Int.equal c 124 (* [comment removed for export] *) then
    (let k := rnum r in
     let nd := Int.div (Int.add k 3) 4 in
     let xi := konst r 5 in
     let xo := konst r 6 in
     let rec digits i skip p :=
       if Int.equal i nd then p else
       let ch := getc r in
       let v := if Int.equal (Int.compare ch 58) -1 then Int.sub ch 48 else Int.sub ch 87 in
       let rec bits j skip p :=
         if Int.equal (Int.compare j 0) -1 then (skip, p)
         else if Int.equal (Int.compare 0 skip) -1 then bits (Int.sub j 1) (Int.sub skip 1) p
         else bits (Int.sub j 1) 0 (make (App (if Int.equal (Int.land (Int.lsr v j) 1) 1 then xi else xo) [| p |])) in
       let (skip', p') := bits 3 skip p in digits (Int.add i 1) skip' p' in
     let p := digits 0 (Int.sub (Int.mul nd 4) k) (konst r 7) in
     let _ := getc r in p)
  else if Int.equal c 126 (* [comment removed for export] *) then make (Uint63 (Uint63.of_int (rdec_acc r 0)))
  else Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "Rpl: bad tag at ") (Message.of_int (r.(pos)))))).

(* [comment removed for export] *)
Ltac2 rcs (r : st) : unit :=
  let k := getc r in
  let a := rlev r in let b := rlev r in
  let ok := (if Int.equal k 108 (* [comment removed for export] *) then Unification.conv Unification.CUMUL TransparentState.full a b
             else if Int.equal k 60 (* [comment removed for export] *) then Unification.conv Unification.CUMUL TransparentState.full (Constr.type a) b
             else if Int.equal k 61 (* [comment removed for export] *) then Unification.conv Unification.CONV TransparentState.full a b
             else fail "Rpl: constraint kind") in
  if ok then () else fail "Rpl: universe constraint not re-derivable".

Ltac2 decode (sty : bool ref) (gl : int -> Std.reference option) (ng : int) (hypt : constr list) (concl : constr) (s : string) : constr :=
  let filler := make (Rel 1) in
  let kc := Array.make 11 None in
  let r0 := { str := s; pos := 0; tab := Array.empty; gl := gl; gc := Array.make ng None; sty := sty; filler := filler; hypt := hypt; concl := concl; kc := kc } in
  let h := getc r0 in
  (if Int.equal h 85 then sty.(contents) := true else ());
  let n := rnum r0 in
  let tab := Array.make n filler in
  let r := { str := s; pos := r0.(pos); tab := tab; gl := gl; gc := r0.(gc); sty := sty; filler := filler; hypt := hypt; concl := concl; kc := kc } in
  let ncs := rnum r in
  let rec csl i := if Int.equal i ncs then () else (rcs r; csl (Int.add i 1)) in csl 0;
  fill r tab 0 n rterm;
  rterm r.

Ltac2 rec lastk (l : (ident * constr option * constr) list) (k : int) : (ident * constr option * constr) list :=
  let n := List.length l in
  if Int.equal (Int.compare k n) -1 then (match l with _ :: t => lastk t k | [] => [] end)
  else l.

Ltac2 rec peel (t : constr) (k : int) : constr :=
  if Int.equal k 0 then t else
  match kind t with
  | Lambda _ b => peel b (Int.sub k 1)
  | _ => fail "Rpl: fewer lambdas than statement binders"
  end.

(* [comment removed for export] *)
Ltac2 run_g (gl : int -> Std.reference option) (ng : int) (k : int) (s : string) : unit :=
  let sty := { contents := false } in
  let hs := (if Int.equal k 0 then [] else lastk (Control.hyps ()) k) in
  let t0 := decode sty gl ng (List.map (fun (h : ident * constr option * constr) => let (_, _, ty) := h in ty) hs) (Control.goal ()) s in
  let t := (if Int.equal k 0 then t0 else
             substnl (List.rev (List.map (fun (h : ident * constr option * constr) => let (i, _, _) := h in make (Var i)) hs)) 0 (peel t0 k)) in
  if sty.(contents) then Control.refine (fun () => t)
  else Std.exact_no_check t.
(* [comment removed for export] *)
Ltac2 run_k (gl : string array) (k : int) (s : string) : unit :=
  run_g (fun g => let p := Array.get gl g in
                  match Env.get (split_path p 0 0 []) with
                  | Some rf => Some rf
                  | None => Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "Rpl: unknown global ") (Message.of_string p))))
                  end) (Array.length gl) k s.
(* [comment removed for export] *)
Ltac2 run_i (gl : ident list array) (k : int) (s : string) : unit :=
  run_g (fun g => Env.get (Array.get gl g)) (Array.length gl) k s.
Ltac2 run (gl : string array) (s : string) : unit := run_k gl 0 s.
End RP.
