(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Ltac2.

Ltac lia_orig := Zify.zify; xlia zchecker.
Ltac nia_orig := Zify.zify; xnia zchecker.

Module LiaRelL2.
  Import Ltac2.
  Import Ltac2.Constr.Unsafe.

  Ltac2 cst (r : Std.reference) : constant := match r with Std.ConstRef c => c | _ => Control.throw Not_found end.
  Ltac2 ind (r : Std.reference) : inductive := match r with Std.IndRef i => i | _ => Control.throw Not_found end.

  (* [comment removed for export] *)
  Ltac2 ctab () : (constant, int) FMap.t :=
    List.fold_left (fun m (r, k) => FMap.add (cst r) k m) (FMap.empty FSet.Tags.constant_tag)
      [ (reference:(Z.add), 1); (reference:(Z.sub), 1); (reference:(Z.opp), 1); (reference:(Z.succ), 1); (reference:(Z.pred), 1);
        (reference:(Z.le), 1); (reference:(Z.lt), 1); (reference:(Z.ge), 1); (reference:(Z.gt), 1);
        (reference:(Z.mul), 2); (reference:(Z.pow), 3);
        (reference:(Z.max), 4); (reference:(Z.min), 4); (reference:(Z.abs), 4); (reference:(not), 4); (reference:(iff), 4);
        (reference:(Z.of_nat), 6); (reference:(Z.of_N), 6); (reference:(Z.to_nat), 6);
        (reference:(lt), 1); (reference:(ge), 1); (reference:(gt), 1);
        (reference:(Nat.add), 1); (reference:(Nat.sub), 1) ].
  Ltac2 itab () : (inductive, int) FMap.t :=
    List.fold_left (fun m (r, k) => FMap.add (ind r) k m) (FMap.empty FSet.Tags.inductive_tag)
      [ (reference:(and), 1); (reference:(or), 4); (reference:(eq), 5); (reference:(le), 1) ].
  (* [comment removed for export] *)
  Ltac2 ttab () : inductive FSet.t :=
    List.fold_left (fun m r => FSet.add (ind r) m) (FSet.empty FSet.Tags.inductive_tag)
      [ reference:(Z); reference:(nat); reference:(N); reference:(positive) ].

  Ltac2 Type tabs := { ct : (constant, int) FMap.t; it : (inductive, int) FMap.t; tt : inductive FSet.t;
                       mutable split : bool; mutable hit : bool; nl : bool }.

  (* [comment removed for export] *)
  Ltac2 is_ctor (c : constr) : bool :=
    match kind c with
    | Constructor _ _ => true
    | App f _ => match kind f with Constructor _ _ => true | _ => false end
    | _ => false
    end.
  Ltac2 is_lit (c : constr) : bool :=
    match kind c with
    | Constructor _ _ => true
    | App f args =>
        match kind f with
        | Constructor _ _ => if Int.equal (Array.length args) 1 then is_ctor (Array.get args 0) else false
        | _ => false
        end
    | _ => false
    end.

  Ltac2 rec mem (c : constr) (l : constr list) : bool :=
    match l with
    | [] => false
    | x :: r => if Constr.equal c x then true else mem c r
    end.
  Ltac2 add (acc : constr list) (c : constr) : constr list := if mem c acc then acc else c :: acc.

  Ltac2 head_class0 (t : tabs) (f : constr) : int :=
    match kind f with
    | Constant k _ => match FMap.find_opt k (t.(ct)) with Some n => n | None => 0 end
    | Ind i _ => match FMap.find_opt i (t.(it)) with Some n => n | None => 0 end
    | _ => 0
    end.
  (* [comment removed for export] *)
  Ltac2 head_class_n (t : tabs) (f : constr) (n : int) : int :=
    let k := head_class0 t f in
    if Int.equal k 0 then 0
    else if Int.equal k 5 then (if Int.equal n 3 then 5 else 0)
    else if Int.equal k 6 then (if Int.equal n 1 then 6 else 0)
    else if Int.equal k 1 then k
    else if Int.equal k 4 then k
    else (if Int.equal n 2 then k else 0).
  Ltac2 arith_type (t : tabs) (ty : constr) : bool :=
    match kind ty with
    | Ind i _ => FSet.mem i (t.(tt))
    | _ => false
    end.

  (* [comment removed for export] *)
  Ltac2 rec atoms (t : tabs) (acc : constr list) (c : constr) : constr list :=
    match kind c with
    | App f args =>
        let k := head_class_n t f (Array.length args) in
        if Int.equal k 1 then Array.fold_left (atoms t) acc args
        else if Int.equal k 2 then
          (let a := Array.get args 0 in let b := Array.get args 1 in
           if is_lit a then atoms t acc b else if is_lit b then atoms t acc a
           else if t.(nl) then atoms t (atoms t acc a) b else add acc c)
        else if Int.equal k 3 then
          (if is_lit (Array.get args 0) then (if is_lit (Array.get args 1) then acc else add acc c) else add acc c)
        else if Int.equal k 4 then (t.(split) := true; Array.fold_left (atoms t) acc args)
        else if Int.equal k 5 then
          (if arith_type t (Array.get args 0) then atoms t (atoms t acc (Array.get args 1)) (Array.get args 2) else add acc c)
        else if Int.equal k 6 then atoms t acc (Array.get args 0)
        else if is_lit c then acc else add acc c
    | Constructor _ _ => acc
    | _ => add acc c
    end.

  (* [comment removed for export] *)
  Ltac2 rec scan (t : tabs) (g : constr list) (c : constr) : unit :=
    match kind c with
    | App f args =>
        let k := head_class_n t f (Array.length args) in
        if Int.equal k 1 then Array.iter (scan t g) args
        else if Int.equal k 2 then
          (let a := Array.get args 0 in let b := Array.get args 1 in
           if is_lit a then scan t g b else if is_lit b then scan t g a
           else if t.(nl) then (scan t g a; scan t g b) else (if mem c g then t.(hit) := true else ()))
        else if Int.equal k 3 then
          (if is_lit (Array.get args 0) then (if is_lit (Array.get args 1) then () else (if mem c g then t.(hit) := true else ()))
           else (if mem c g then t.(hit) := true else ()))
        else if Int.equal k 4 then (t.(split) := true; Array.iter (scan t g) args)
        else if Int.equal k 5 then
          (if arith_type t (Array.get args 0) then (scan t g (Array.get args 1); scan t g (Array.get args 2))
           else (if mem c g then t.(hit) := true else ()))
        else if Int.equal k 6 then scan t g (Array.get args 0)
        else if is_lit c then () else (if mem c g then t.(hit) := true else ())
    | Constructor _ _ => ()
    | _ => if mem c g then t.(hit) := true else ()
    end.

  (* [comment removed for export] *)
  Ltac2 arith_head (t : tabs) (c : constr) : bool :=
    match kind c with
    | App f args =>
        let k := head_class_n t f (Array.length args) in
        if Int.equal k 5 then arith_type t (Array.get args 0)
        else if Int.equal k 1 then true else Int.equal k 4
    | _ => false
    end.

  Ltac2 rec shares (l : constr list) (g : constr list) : bool :=
    match l with
    | [] => false
    | x :: r => if mem x g then true else shares r g
    end.

  (* [comment removed for export] *)
  Ltac2 arith_hyps (t : tabs) (with_splits : bool) : (ident * constr list) list :=
    List.fold_left (fun acc (id, _, ty) =>
                      if arith_head t ty then
                        (t.(split) := false;
                         let ats := atoms t [] ty in
                         if with_splits then (id, ats) :: acc
                         else if t.(split) then acc else (id, ats) :: acc)
                      else acc) [] (Control.hyps ()).

  (* [comment removed for export] *)
  Ltac2 rec round (rel : constr list) (todo : (ident * constr list) list)
      (kept : ident list) (rest : (ident * constr list) list) (nw : constr list)
      : ident list * (ident * constr list) list * constr list :=
    match todo with
    | [] => (kept, rest, nw)
    | h :: r =>
        let (id, ats) := h in
        if shares ats rel then round rel r (id :: kept) rest (List.append ats nw)
        else round rel r kept (h :: rest) nw
    end.

  Ltac2 rec close (hops : int) (rel : constr list) (todo : (ident * constr list) list) (kept : ident list) : ident list :=
    if Int.le hops 0 then kept else
    let (kept', rest, nw) := round rel todo kept [] [] in
    match nw with
    | [] => kept'
    | _ => close (Int.sub hops 1) (List.append nw rel) rest kept'
    end.

  Ltac2 mk_tabs_nl (n : bool) : tabs := { ct := ctab (); it := itab (); tt := ttab (); split := false; hit := false; nl := n }.
  Ltac2 mk_tabs () : tabs := mk_tabs_nl false.

  (* [comment removed for export] *)
  Ltac2 hop1 (t : tabs) (g : constr list) (with_splits : bool) : ident list :=
    List.fold_left (fun acc (id, _, ty) =>
                      if arith_head t ty then
                        (t.(split) := false; t.(hit) := false; scan t g ty;
                         if t.(hit) then (if with_splits then id :: acc else if t.(split) then acc else id :: acc) else acc)
                      else acc) [] (Control.hyps ()).

  (* [comment removed for export] *)
  Ltac2 prune_gen (n : bool) (hops : int) (with_splits : bool) : unit :=
    let t := mk_tabs_nl n in
    let g := atoms t [] (Control.goal ()) in
    match g with
    | [] => Std.keep []                                   (* [comment removed for export] *)
    | _ => if Int.equal hops 1 then Std.keep (hop1 t g with_splits)
           else Std.keep (close hops g (arith_hyps t with_splits) [])
    end.
  Ltac2 prune (hops : int) (with_splits : bool) : unit := prune_gen false hops with_splits.
  Ltac2 prune_all (with_splits : bool) : unit :=
    let t := mk_tabs () in
    Std.keep (List.map (fun (id, _) => id) (arith_hyps t with_splits)).
  (* [comment removed for export] *)
  Ltac2 rec mem_id (x : ident) (l : ident list) : bool :=
    match l with
    | [] => false
    | y :: r => if Ident.equal x y then true else mem_id x r
    end.
  Ltac2 pin (keep : ident list) : unit :=
    let t := mk_tabs () in
    List.iter (fun (id, _, ty) =>
                 if arith_head t ty then
                   (if mem_id id keep then () else Control.plus (fun () => Std.clear [id]) (fun _ => ()))
                 else ()) (Control.hyps ()).
  Ltac2 p1 () : unit := prune 1 false.
  Ltac2 p1s () : unit := prune 1 true.
  Ltac2 p2 () : unit := prune 2 false.
  Ltac2 p2s () : unit := prune 2 true.
  Ltac2 pa () : unit := prune_all false.
  (* [comment removed for export] *)
  Ltac2 n1 () : unit := prune_gen true 1 false.
  Ltac2 n1s () : unit := prune_gen true 1 true.
  Ltac2 n2 () : unit := prune_gen true 2 false.

  (* [comment removed for export] *)
  Ltac2 rec len (l : ident list) : int := match l with [] => 0 | _ :: r => Int.add 1 (len r) end.
  Ltac2 attempt (tac : unit -> unit) (keep : ident list) : bool :=
    Control.plus (fun () => Control.once (fun () => Std.keep keep; tac (); true)) (fun _ => false).
  (* [comment removed for export] *)
  Ltac2 hop1_both (t : tabs) (g : constr list) : ident list * ident list :=
    List.fold_left (fun (a, b) (id, _, ty) =>
                      if arith_head t ty then
                        (t.(split) := false; t.(hit) := false; scan t g ty;
                         if t.(hit) then (if t.(split) then (a, id :: b) else (id :: a, id :: b)) else (a, b))
                      else (a, b)) ([], []) (Control.hyps ()).
  Ltac2 arith_hyps_both (t : tabs) : (ident * constr list) list * (ident * constr list) list :=
    List.fold_left (fun (a, b) (id, _, ty) =>
                      if arith_head t ty then
                        (t.(split) := false;
                         let ats := atoms t [] ty in
                         if t.(split) then (a, (id, ats) :: b) else ((id, ats) :: a, (id, ats) :: b))
                      else (a, b)) ([], []) (Control.hyps ()).
  Ltac2 run (n : bool) (tac : unit -> unit) : unit :=
    let t := mk_tabs_nl n in
    let g := atoms t [] (Control.goal ()) in
    let ok :=
      match g with
      | [] => attempt tac []                                   (* [comment removed for export] *)
      | _ =>
          let (s1, s1s) := hop1_both t g in
          if attempt tac s1 then true
          else if (if Int.equal (len s1s) (len s1) then false else attempt tac s1s) then true
          else
            match s1s with
            | [] => false                                      (* [comment removed for export] *)
            | _ =>
                let (hn, ha) := arith_hyps_both t in
                let s2 := close 2 g hn [] in
                if (if Int.equal (len s2) (len s1) then false else attempt tac s2) then true
                else
                  let s2s := close 2 g ha [] in
                  if (if Int.equal (len s2s) (len s2) then false
                      else if Int.equal (len s2s) (len s1s) then false else attempt tac s2s) then true
                  else
                    let sa := List.map (fun (id, _) => id) hn in
                    if Int.equal (len sa) (len s2) then false else attempt tac sa
            end
      end in
    if ok then () else Control.zero (Tactic_failure None).
  Ltac2 run_lia () : unit := run false (fun () => ltac1:(lia_orig)).
  Ltac2 run_nia () : unit := run true (fun () => ltac1:(nia_orig)).
End LiaRelL2.

Ltac lia_p1 := ltac2:(LiaRelL2.p1 ()).
Ltac lia_p1s := ltac2:(LiaRelL2.p1s ()).
Ltac lia_p2 := ltac2:(LiaRelL2.p2 ()).
Ltac lia_p2s := ltac2:(LiaRelL2.p2s ()).
Ltac lia_pa := ltac2:(LiaRelL2.pa ()).
Ltac nia_n1 := ltac2:(LiaRelL2.n1 ()).
Ltac nia_n1s := ltac2:(LiaRelL2.n1s ()).
Ltac nia_n2 := ltac2:(LiaRelL2.n2 ()).
(* [comment removed for export] *)
Ltac nia_rel := first [ ltac2:(LiaRelL2.run_nia ()) | nia_orig ].
Ltac lia_rel := first [ ltac2:(LiaRelL2.run_lia ()) | lia_orig ].
