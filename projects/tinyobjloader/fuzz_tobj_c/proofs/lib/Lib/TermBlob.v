(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Corelib Require BinNums.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Env Ident String Char Array Control Message Int List.

Ltac2 Type exn ::= [ TermBlobError (string) ].
Ltac2 tb_fail (s : string) := Control.throw (TermBlobError s).

Ltac2 hexval (c : char) : int :=
  let n := Char.to_int c in
  if Int.le 48 n then (if Int.le n 57 then Int.sub n 48 else
    if Int.le 97 n then (if Int.le n 102 then Int.sub n 87 else -1) else -1) else -1.

Ltac2 is_space (c : char) : bool :=
  let n := Char.to_int c in
  if Int.equal n 32 then true else if Int.equal n 10 then true else if Int.equal n 13 then true else Int.equal n 9.

(* [comment removed for export] *)
Ltac2 rec skip (s : string) (i : int) (len : int) : int :=
  if Int.lt i len then (if is_space (String.get s i) then skip s (Int.add i 1) len else i) else i.

(* [comment removed for export] *)
Ltac2 rec num_aux (s : string) (i : int) (len : int) (acc : int) : int * int :=
  if Int.lt i len then
    let d := hexval (String.get s i) in
    if Int.lt d 0 then (acc, i) else num_aux s (Int.add i 1) len (Int.add (Int.mul acc 16) d)
  else (acc, i).
Ltac2 num (s : string) (i : int) (len : int) : int * int := num_aux s (skip s i len) len 0.

(* [comment removed for export] *)
Ltac2 rec hexend (s : string) (i : int) (len : int) : int :=
  if Int.lt i len then (if Int.lt (hexval (String.get s i)) 0 then i else hexend s (Int.add i 1) len) else i.

Ltac2 gref_of_path (p : string) : Std.reference :=
  let rec sp_path (i : int) (start : int) (acc : ident list) : ident list :=
    if Int.equal i (String.length p) then
      (match Ident.of_string (String.sub p start (Int.sub i start)) with Some id => List.rev (id :: acc) | None => tb_fail p end)
    else if Int.equal (Char.to_int (String.get p i)) 46 then
      (match Ident.of_string (String.sub p start (Int.sub i start)) with Some id => sp_path (Int.add i 1) (Int.add i 1) (id :: acc) | None => tb_fail p end)
    else sp_path (Int.add i 1) start acc in
  match Env.get (sp_path 0 0 []) with
  | Some r => r
  | None => tb_fail (String.app "TermBlob: unknown global " p)
  end.
Ltac2 ref_of_path (p : string) : constr := Env.instantiate (gref_of_path p).

(* [comment removed for export] *)
Ltac2 symtab (l : string list) : string array * string array :=
  let n := List.fold_left (fun k e => if Int.equal (String.length e) 0 then k else if Int.equal (Char.to_int (String.get e 0)) 64 then k else Int.add k 1) 0 l in
  let names := Array.make (Int.add n 1) "" in
  let mods := Array.make (Int.add n 1) "" in
  let rec fill (l : string list) (k : int) (cur : string) : unit :=
    match l with
    | [] => ()
    | e :: l' =>
        if Int.equal (String.length e) 0 then fill l' k cur
        else if Int.equal (Char.to_int (String.get e 0)) 64 then fill l' k (String.sub e 1 (Int.sub (String.length e) 1))
        else (Array.set names k e; Array.set mods k cur; fill l' (Int.add k 1) cur)
    end in
  fill l 0 ""; (names, mods).
Ltac2 sym_path (tab : string array * string array) (k : int) : string :=
  let (names, mods) := tab in
  let m := Array.get mods k in
  if Int.equal (String.length m) 0 then Array.get names k else String.app m (String.app "." (Array.get names k)).

(* [comment removed for export] *)
Ltac2 positive_of_hex (xI : constr) (xO : constr) (xH : constr) (s : string) (i : int) (j : int) : constr :=
  let app1 (f : constr) (a : constr) := Constr.Unsafe.make (Constr.Unsafe.App f (Array.make 1 a)) in
  let rec bits (acc : constr option) (k : int) : constr option :=
    if Int.lt k j then
      let d := hexval (String.get s k) in
      let step (acc : constr option) (b : int) : constr option :=
        match acc with
        | None => if Int.equal b 0 then None else Some xH
        | Some p => Some (app1 (if Int.equal b 0 then xO else xI) p)
        end in
      let b3 := Int.div d 8 in let r3 := Int.sub d (Int.mul b3 8) in
      let b2 := Int.div r3 4 in let r2 := Int.sub r3 (Int.mul b2 4) in
      let b1 := Int.div r2 2 in let b0 := Int.sub r2 (Int.mul b1 2) in
      bits (step (step (step (step acc b3) b2) b1) b0) (Int.add k 1)
    else acc in
  match bits None i with Some p => p | None => tb_fail "TermBlob: positive literal 0" end.

(* [comment removed for export] *)
Ltac2 dec_term_gen (ext : string list) (s : string) : constr :=
  let len := String.length s in
  let (nsym, i0) := num s 0 len in
  (* [comment removed for export] *)
  let rec rdsyms (k : int) (i : int) (acc : string list) : int * string list :=
    if Int.equal k nsym then (i, List.rev acc) else
      let rec fin (j : int) : int := if Int.equal (Char.to_int (String.get s j)) 124 then j else fin (Int.add j 1) in
      let i := skip s i len in
      let j := fin i in
      let e := String.sub s i (Int.sub j i) in
      rdsyms (if Int.equal (Char.to_int (String.get e 0)) 64 then k else Int.add k 1) (Int.add j 1) (e :: acc) in
  let (i1, own) := rdsyms 0 (Int.add (skip s i0 len) 1) [] in
  let tab := symtab (if Int.equal nsym 0 then ext else own) in
  let extres := Array.make (Int.add (Array.length (fst tab)) 1) None in
  let (nmemo, i2) := num s i1 len in
  let memo := Array.make (Int.add nmemo 1) constr:(tt) in
  let xI := constr:(BinNums.xI) in let xO := constr:(BinNums.xO) in let xH := constr:(BinNums.xH) in
  let zpos := constr:(BinNums.Zpos) in let zneg := constr:(BinNums.Zneg) in let z0 := constr:(BinNums.Z0) in
  let npos := constr:(BinNums.Npos) in let n0 := constr:(BinNums.N0) in let cS := constr:(S) in let cO := constr:(O) in
  let app1 (f : constr) (a : constr) := Constr.Unsafe.make (Constr.Unsafe.App f (Array.make 1 a)) in
  let rec popn (n : int) (st : constr list) (acc : constr list) : constr list * constr list :=
    if Int.equal n 0 then (acc, st) else
    match st with x :: st' => popn (Int.sub n 1) st' (x :: acc) | [] => tb_fail "TermBlob: stack underflow" end in
  let rec nat_of (n : int) (acc : constr) : constr := if Int.equal n 0 then acc else nat_of (Int.sub n 1) (app1 cS acc) in
  let rec go (i : int) (st : constr list) : constr :=
    let i := skip s i len in
    if Int.le len i then (match st with [x] => x | _ => tb_fail "TermBlob: bad final stack" end) else
    let c := Char.to_int (String.get s i) in
    let i := Int.add i 1 in
    if Int.equal c 83 (* [comment removed for export] *) then let (k, j) := num s i len in
      let t := match Array.get extres k with
               | Some t => t
               | None => let t := ref_of_path (sym_path tab k) in Array.set extres k (Some t); t end in
      go j (t :: st)
    else if Int.equal c 88 (* [comment removed for export] *) then let (k, j) := num s i len in
      let (n, j2) := num s (Int.add (skip s j len) 1) len in
      let (brs, st1) := popn n st [] in
      (match st1 with
       | scrut :: ret :: st2 =>
           (match gref_of_path (sym_path tab k) with
            | Std.IndRef ind =>
                go j2 (Constr.Unsafe.make (Constr.Unsafe.Case (Constr.Unsafe.case ind) (ret, Constr.Binder.Relevant) Constr.Unsafe.NoInvert scrut (Array.of_list brs)) :: st2)
            | _ => tb_fail "TermBlob: X on a non-inductive" end)
       | _ => tb_fail "TermBlob: X underflow" end)
    else if Int.equal c 71 (* [comment removed for export] *) then let (k, j) := num s i len in go j (Array.get memo k :: st)
    else if Int.equal c 77 (* [comment removed for export] *) then let (k, j) := num s i len in
      (match st with x :: _ => Array.set memo k x; go j st | [] => tb_fail "TermBlob: M on empty stack" end)
    else if Int.equal c 65 (* [comment removed for export] *) then let (n, j) := num s i len in
      let (args, st1) := popn n st [] in
      (match st1 with
       | f :: st2 => go j (Constr.Unsafe.make (Constr.Unsafe.App f (Array.of_list args)) :: st2)
       | [] => tb_fail "TermBlob: A without head" end)
    else if Int.equal c 80 (* [comment removed for export] *) then let i := skip s i len in let j := hexend s i len in go j (positive_of_hex xI xO xH s i j :: st)
    else if Int.equal c 90 (* [comment removed for export] *) then let i := skip s i len in let j := hexend s i len in
      let (v, _) := num s i len in
      go j ((if Int.equal (Int.sub j i) 1 then (if Int.equal v 0 then z0 else app1 zpos (positive_of_hex xI xO xH s i j)) else app1 zpos (positive_of_hex xI xO xH s i j)) :: st)
    else if Int.equal c 78 (* [comment removed for export] *) then let i := skip s i len in let j := hexend s i len in go j (app1 zneg (positive_of_hex xI xO xH s i j) :: st)
    else if Int.equal c 81 (* [comment removed for export] *) then let i := skip s i len in let j := hexend s i len in
      let (v, _) := num s i len in
      go j ((if Int.equal (Int.sub j i) 1 then (if Int.equal v 0 then n0 else app1 npos (positive_of_hex xI xO xH s i j)) else app1 npos (positive_of_hex xI xO xH s i j)) :: st)
    else if Int.equal c 85 (* [comment removed for export] *) then let (n, j) := num s i len in go j (nat_of n cO :: st)
    else if Int.equal c 82 (* [comment removed for export] *) then let (k, j) := num s i len in go j (Constr.Unsafe.make (Constr.Unsafe.Rel k) :: st)
    else if Int.equal c 86 (* [comment removed for export] *) then
      let i := skip s i len in
      let rec fin (j : int) : int := if Int.equal (Char.to_int (String.get s j)) 59 then j else fin (Int.add j 1) in
      let j := fin i in
      (match Ident.of_string (String.sub s i (Int.sub j i)) with
       | Some id => go (Int.add j 1) (Constr.Unsafe.make (Constr.Unsafe.Var id) :: st)
       | None => tb_fail "TermBlob: bad variable name" end)
    else if Int.equal c 79 (* [comment removed for export] *) then go i (constr:(Prop) :: st)
    else if Int.equal c 69 (* [comment removed for export] *) then go i (constr:(Set) :: st)
    else if Int.equal c 70 (* [comment removed for export] *) then bind 0 i st
    else if Int.equal c 76 (* [comment removed for export] *) then bind 1 i st
    else if Int.equal c 84 (* [comment removed for export] *) then bind 2 i st
    else tb_fail "TermBlob: bad opcode"
  with bind (k : int) (i : int) (st : constr list) : constr :=
    let i := skip s i len in
    let rec fin (j : int) : int := if Int.equal (Char.to_int (String.get s j)) 59 then j else fin (Int.add j 1) in
    let j := fin i in
    let nm := String.sub s i (Int.sub j i) in
    let name := if String.equal nm "_" then None else (match Ident.of_string nm with Some id => Some id | None => tb_fail "TermBlob: bad binder name" end) in
    let mk (ty : constr) := Constr.Binder.unsafe_make name Constr.Binder.Relevant ty in
    if Int.equal k 2 then
      (match st with
       | body :: ty :: v :: st' => go (Int.add j 1) (Constr.Unsafe.make (Constr.Unsafe.LetIn (mk ty) v body) :: st')
       | _ => tb_fail "TermBlob: T underflow" end)
    else
      (match st with
       | body :: ty :: st' =>
           go (Int.add j 1) (Constr.Unsafe.make (if Int.equal k 0 then Constr.Unsafe.Prod (mk ty) body else Constr.Unsafe.Lambda (mk ty) body) :: st')
       | _ => tb_fail "TermBlob: binder underflow" end) in
  go (Int.add (skip s i2 len) 1) [].

Ltac2 dec_term (s : string) : constr := dec_term_gen [] s.

(* [comment removed for export] *)
Ltac2 dec (s : string) : unit := let t := dec_term s in Control.refine (fun () => t).
Ltac2 dec2 (tbl : string list) (s : string) : unit := let t := dec_term_gen tbl s in Control.refine (fun () => t).
