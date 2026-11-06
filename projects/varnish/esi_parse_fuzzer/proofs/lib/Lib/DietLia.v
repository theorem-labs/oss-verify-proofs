(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia.
From Stdlib Require Import Zify PreOmega.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import LiaTwx2.
From Ltac2 Require Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RL.
  Import Ltac2.
  Ltac2 const_set (l : Std.reference list) : constant FSet.t :=
    List.fold_left (fun s r => match r with Std.ConstRef k => FSet.add k s | _ => s end)
      (FSet.empty FSet.Tags.constant_tag) l.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac2 mutable max_logic : int := 6.
  Ltac2 mutable debug : bool := false.
  Ltac2 mutable sec : bool := false.
  Ltac2 mutable strict : bool := false.
  Ltac2 nonstrict () : unit := if strict then Control.zero (Tactic_failure (Some (Message.of_string "diet: strict mode"))) else ().

  (* [comment removed for export] *)
  Ltac2 op_consts () : constant FSet.t := const_set [
    reference:(Z.add); reference:(Z.sub); reference:(Z.mul); reference:(Z.opp); reference:(Z.succ); reference:(Z.pred);
    reference:(Z.of_nat); reference:(Z.to_nat); reference:(Z.of_N); reference:(Z.to_N); reference:(Z.max); reference:(Z.min);
    reference:(Z.abs); reference:(Z.div); reference:(Z.modulo); reference:(Z.quot); reference:(Z.rem); reference:(Z.pow);
    reference:(Nat.add); reference:(Nat.sub); reference:(Nat.mul); reference:(Nat.div); reference:(Nat.modulo);
    reference:(Nat.min); reference:(Nat.max); reference:(Nat.pred);
    reference:(N.add); reference:(N.sub); reference:(N.mul); reference:(N.of_nat) ].
  (* [comment removed for export] *)
  Ltac2 mul_consts () : constant FSet.t := const_set [
    reference:(Z.mul); reference:(Z.div); reference:(Z.modulo); reference:(Z.quot); reference:(Z.rem); reference:(Z.pow);
    reference:(Z.max); reference:(Z.min); reference:(Z.abs); reference:(Z.to_nat); reference:(Z.to_N);
    reference:(Nat.mul); reference:(Nat.div); reference:(Nat.modulo); reference:(Nat.sub); reference:(Nat.min);
    reference:(Nat.max); reference:(Nat.pred); reference:(N.mul); reference:(N.sub) ].
  Ltac2 dm_consts () : constant FSet.t := const_set [
    reference:(Z.div); reference:(Z.modulo); reference:(Z.quot); reference:(Z.rem); reference:(Nat.div); reference:(Nat.modulo) ].
  (* [comment removed for export] *)
  Ltac2 rel_consts () : constant FSet.t := const_set [
    reference:(Z.le); reference:(Z.lt); reference:(Z.ge); reference:(Z.gt); reference:(Z.divide);
    reference:(lt); reference:(ge); reference:(gt); reference:(N.le); reference:(N.lt) ].

  (* [comment removed for export] *)
  Ltac2 rec has_evar (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.Evar _ _ => true
    | Constr.Unsafe.App h args => if has_evar h then true else Array.exist has_evar args
    | Constr.Unsafe.Cast u _ ty => if has_evar u then true else has_evar ty
    | Constr.Unsafe.Prod b body => if has_evar (Constr.Binder.type b) then true else has_evar body
    | Constr.Unsafe.Lambda b body => if has_evar (Constr.Binder.type b) then true else has_evar body
    | Constr.Unsafe.LetIn b v body => if has_evar (Constr.Binder.type b) then true else if has_evar v then true else has_evar body
    | Constr.Unsafe.Case _ rt _ scrut brs =>
        let (r, _) := rt in
        if has_evar r then true else if has_evar scrut then true else Array.exist has_evar brs
    | Constr.Unsafe.Fix _ _ bs ts =>
        if Array.exist (fun b => has_evar (Constr.Binder.type b)) bs then true else Array.exist has_evar ts
    | Constr.Unsafe.CoFix _ bs ts =>
        if Array.exist (fun b => has_evar (Constr.Binder.type b)) bs then true else Array.exist has_evar ts
    | Constr.Unsafe.Proj _ _ u => has_evar u
    | Constr.Unsafe.Array _ vals d ty =>
        if Array.exist has_evar vals then true else if has_evar d then true else has_evar ty
    | _ => false
    end.

  (* [comment removed for export] *)
  Ltac2 Type st := {
    mutable bv : (ident, (constr * int) list) FMap.t;
    mutable bk : (constant, (constr * int) list) FMap.t;
    mutable bo : (constr * int) list;
    mutable n : int }.
  Ltac2 Type key := [ KVar (ident) | KConst (constant) | KOther ].
  Ltac2 key_of (t : constr) : key :=
    let hd (h : constr) := match Constr.Unsafe.kind h with
      | Constr.Unsafe.Var id => KVar id
      | Constr.Unsafe.Constant k _ => KConst k
      | _ => KOther end in
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h _ => hd h
    | _ => hd t
    end.
  Ltac2 rec assoc_atom (t : constr) (l : (constr * int) list) : int option :=
    match l with
    | [] => None
    | p :: r => let (a, i) := p in if Constr.equal t a then Some i else assoc_atom t r
    end.
  Ltac2 intern (s : st) (insert : bool) (t : constr) : int option :=
    let fresh () := let i := s.(n) in s.(n) := Int.add i 1; i in
    match key_of t with
    | KVar id =>
        let l := match FMap.find_opt id (s.(bv)) with Some l => l | None => [] end in
        (match assoc_atom t l with
         | Some i => Some i
         | None => if insert then (let i := fresh () in s.(bv) := FMap.add id ((t, i) :: l) (s.(bv)); Some i) else None
         end)
    | KConst k =>
        let l := match FMap.find_opt k (s.(bk)) with Some l => l | None => [] end in
        (match assoc_atom t l with
         | Some i => Some i
         | None => if insert then (let i := fresh () in s.(bk) := FMap.add k ((t, i) :: l) (s.(bk)); Some i) else None
         end)
    | KOther =>
        (match assoc_atom t (s.(bo)) with
         | Some i => Some i
         | None => if insert then (let i := fresh () in s.(bo) := (t, i) :: s.(bo); Some i) else None
         end)
    end.

  (* [comment removed for export] *)
  Ltac2 Type col := { mutable ats : int list; mutable simple : bool; mutable dm : bool }.
  Ltac2 rec mem_int (i : int) (l : int list) : bool :=
    match l with [] => false | x :: r => if Int.equal i x then true else mem_int i r end.
  (* [comment removed for export] *)
  Ltac2 rec term_atoms (ops : constant FSet.t) (muls : constant FSet.t) (dms : constant FSet.t) (deep : bool)
                       (s : st) (insert : bool) (c : col) (mul : bool) (t : constr) : unit :=
    let atom () :=
      match intern s insert t with
      | Some i => (if mul then c.(simple) := false else ()); if mem_int i (c.(ats)) then () else c.(ats) := i :: c.(ats)
      | None => ()
      end in
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h args =>
        match Constr.Unsafe.kind h with
        | Constr.Unsafe.Constant k _ =>
            if FSet.mem k ops then
              (if FSet.mem k dms then
                 (c.(dm) := true;
                  if deep then Array.iter (term_atoms ops muls dms deep s insert c true) args else atom ())
               else
                 (let mul' := if mul then true else FSet.mem k muls in
                  Array.iter (term_atoms ops muls dms deep s insert c mul') args))
            else atom ()
        | Constr.Unsafe.Constructor _ _ => Array.iter (term_atoms ops muls dms deep s insert c mul) args
        | Constr.Unsafe.Ind _ _ => ()
        | _ => atom ()
        end
    | Constr.Unsafe.Constructor _ _ => ()
    | Constr.Unsafe.Ind _ _ => ()
    | Constr.Unsafe.Sort _ => ()
    | Constr.Unsafe.Cast u _ _ => term_atoms ops muls dms deep s insert c mul u
    | _ => atom ()
    end.

  (* [comment removed for export] *)
  Ltac2 arith_ty (t : constr) : bool :=
    if Constr.equal t 'Z then true else if Constr.equal t 'nat then true
    else if Constr.equal t 'N then true else Constr.equal t 'positive.
  (* [comment removed for export] *)
  Ltac2 rec plain_parts (rels : constant FSet.t) (acc : constr list) (t : constr) : constr list option :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h args =>
        match Constr.Unsafe.kind h with
        | Constr.Unsafe.Constant k _ => if FSet.mem k rels then Some (t :: acc) else None
        | Constr.Unsafe.Ind _ _ =>
            if Constr.equal h '@and then
              (match plain_parts rels acc (Array.get args 0) with
               | Some acc => plain_parts rels acc (Array.get args 1)
               | None => None end)
            else if Constr.equal h '@eq then (if arith_ty (Array.get args 0) then Some (t :: acc) else None)
            else if Constr.equal h '@le then Some (t :: acc)
            else None
        | _ => None
        end
    | Constr.Unsafe.Ind _ _ => if Constr.equal t 'True then Some acc else None
    | _ => None
    end.
  (* [comment removed for export] *)
  Ltac2 rec logical (rels : constant FSet.t) (t : constr) : bool :=
    match plain_parts rels [] t with
    | Some _ => true
    | None =>
        match Constr.Unsafe.kind t with
        | Constr.Unsafe.App h args =>
            if Constr.equal h '@and then (if logical rels (Array.get args 0) then logical rels (Array.get args 1) else false)
            else if Constr.equal h '@or then (if logical rels (Array.get args 0) then logical rels (Array.get args 1) else false)
            else if Constr.equal h '@iff then (if logical rels (Array.get args 0) then logical rels (Array.get args 1) else false)
            else if Constr.equal h '@not then logical rels (Array.get args 0)
            else false
        | Constr.Unsafe.Prod b body =>
            if Constr.Unsafe.closedn 0 body then (if logical rels (Constr.Binder.type b) then logical rels body else false) else false
        | Constr.Unsafe.Ind _ _ => Constr.equal t 'False
        | _ => false
        end
    end.
  (* [comment removed for export] *)
  Ltac2 rec stmt_atoms (ops : constant FSet.t) (muls : constant FSet.t) (dms : constant FSet.t) (rels : constant FSet.t)
                       (deep : bool) (s : st) (insert : bool) (c : col) (t : constr) : unit :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h args =>
        match Constr.Unsafe.kind h with
        | Constr.Unsafe.Constant k _ =>
            if FSet.mem k rels then Array.iter (term_atoms ops muls dms deep s insert c false) args
            else if Constr.equal h '@not then Array.iter (stmt_atoms ops muls dms rels deep s insert c) args
            else if Constr.equal h '@iff then Array.iter (stmt_atoms ops muls dms rels deep s insert c) args
            else ()
        | Constr.Unsafe.Ind _ _ =>
            if Constr.equal h '@eq then
              (if arith_ty (Array.get args 0) then
                 (term_atoms ops muls dms deep s insert c false (Array.get args 1);
                  term_atoms ops muls dms deep s insert c false (Array.get args 2))
               else ())
            else if Constr.equal h '@le then Array.iter (term_atoms ops muls dms deep s insert c false) args
            else if Constr.equal h '@and then Array.iter (stmt_atoms ops muls dms rels deep s insert c) args
            else if Constr.equal h '@or then Array.iter (stmt_atoms ops muls dms rels deep s insert c) args
            else ()
        | _ => ()
        end
    | Constr.Unsafe.Prod b body =>
        stmt_atoms ops muls dms rels deep s insert c (Constr.Binder.type b); stmt_atoms ops muls dms rels deep s insert c body
    | _ => ()
    end.

  (* [comment removed for export] *)
  Ltac2 Type table := {
    t_st : st;
    t_ops : constant FSet.t; t_muls : constant FSet.t; t_dms : constant FSet.t; t_rels : constant FSet.t;
    t_catoms : int list array;      (* [comment removed for export] *)
    t_cdeep : int list array;       (* [comment removed for export] *)
    t_chyp : int array;             (* [comment removed for export] *)
    t_csimple : bool array;         (* [comment removed for export] *)
    t_clogic : bool array;          (* [comment removed for export] *)
    t_hid : ident array;            (* [comment removed for export] *)
    t_hclear : bool array;          (* [comment removed for export] *)
    t_hdm : bool array;             (* [comment removed for export] *)
    t_hlogic : bool array;          (* [comment removed for export] *)
    t_hevar : bool array;           (* [comment removed for export] *)
    t_others : ident list;          (* [comment removed for export] *)
    t_known : ident FSet.t;         (* [comment removed for export] *)
    t_natoms : int }.

  Ltac2 build (sec : bool) : table :=
    let ops := op_consts () in let muls := mul_consts () in let dms := dm_consts () in let rels := rel_consts () in
    let s := { bv := FMap.empty FSet.Tags.ident_tag; bk := FMap.empty FSet.Tags.constant_tag; bo := []; n := 0 } in
    (* [comment removed for export] *)
    let cats := { contents := [] } in let cdeep := { contents := [] } in let chyp := { contents := [] } in
    let known := { contents := FSet.empty FSet.Tags.ident_tag } in
    let csim := { contents := [] } in let clog := { contents := [] } in
    let hid := { contents := [] } in let hcl := { contents := [] } in let hdm := { contents := [] } in
    let hlg := { contents := [] } in let hev := { contents := [] } in
    let others := { contents := [] } in
    let nh := { contents := 0 } in
    List.iter (fun h => let (id, body, ty) := h in
      known.(contents) := FSet.add id (known.(contents));
      match body with
      | Some _ => ()
      | None =>
          let loc := zt_is_local id in
          let add_hyp (parts : constr list) (logic : bool) :=
            let hi := nh.(contents) in
            nh.(contents) := Int.add hi 1;
            let anydm := { contents := false } in
            List.iter (fun p =>
              let c := { ats := []; simple := true; dm := false } in
              stmt_atoms ops muls dms rels false s true c p;
              (if c.(dm) then anydm.(contents) := true else ());
              cats.(contents) := c.(ats) :: cats.(contents);
              (if c.(dm) then
                 (let c2 := { ats := []; simple := true; dm := false } in
                  stmt_atoms ops muls dms rels true s true c2 p;
                  cdeep.(contents) := c2.(ats) :: cdeep.(contents))
               else cdeep.(contents) := c.(ats) :: cdeep.(contents));
              chyp.(contents) := hi :: chyp.(contents);
              csim.(contents) := (if logic then false else c.(simple)) :: csim.(contents);
              clog.(contents) := logic :: clog.(contents)) parts;
            hid.(contents) := id :: hid.(contents);
            hcl.(contents) := (if loc then true else sec) :: hcl.(contents);
            hdm.(contents) := anydm.(contents) :: hdm.(contents);
            hlg.(contents) := logic :: hlg.(contents);
            hev.(contents) := false :: hev.(contents) in
          match plain_parts rels [] ty with
          | Some parts =>
              (* [comment removed for export] *)
              if has_evar ty then (if loc then others.(contents) := id :: others.(contents) else ())
              else add_hyp parts false
          | None =>
              if logical rels ty then
                (if has_evar ty then (if loc then others.(contents) := id :: others.(contents) else ())
                 else add_hyp [ty] true)
              else if loc then (if zt_is_prop ty then others.(contents) := id :: others.(contents) else ())
              else ()
          end
      end) (Control.hyps ());
    { t_st := s; t_ops := ops; t_muls := muls; t_dms := dms; t_rels := rels;
      t_catoms := Array.of_list (List.rev (cats.(contents)));
      t_cdeep := Array.of_list (List.rev (cdeep.(contents)));
      t_chyp := Array.of_list (List.rev (chyp.(contents)));
      t_csimple := Array.of_list (List.rev (csim.(contents)));
      t_clogic := Array.of_list (List.rev (clog.(contents)));
      t_hid := Array.of_list (List.rev (hid.(contents)));
      t_hclear := Array.of_list (List.rev (hcl.(contents)));
      t_hdm := Array.of_list (List.rev (hdm.(contents)));
      t_hlogic := Array.of_list (List.rev (hlg.(contents)));
      t_hevar := Array.of_list (List.rev (hev.(contents)));
      t_others := others.(contents);
      t_known := known.(contents);
      t_natoms := s.(n) }.

  Ltac2 rec exists_int (f : int -> bool) (l : int list) : bool :=
    match l with [] => false | x :: r => if f x then true else exists_int f r end.

  (* [comment removed for export] *)
  Ltac2 query (tb : table) (logic : bool) : bool :=
    let nc := Array.length (tb.(t_catoms)) in
    let nh := Array.length (tb.(t_hid)) in
    let na := tb.(t_natoms) in
    (* [comment removed for export] *)
    let g := Control.goal () in
    (if has_evar g then Control.zero (Tactic_failure (Some (Message.of_string "diet: goal with existential variables"))) else ());
    let gc0 := { ats := []; simple := true; dm := false } in
    stmt_atoms (tb.(t_ops)) (tb.(t_muls)) (tb.(t_dms)) (tb.(t_rels)) false (tb.(t_st)) false gc0 g;
    (* [comment removed for export] *)
    let deep := gc0.(dm) in
    let gc := if deep then
        (let c := { ats := []; simple := true; dm := true } in
         stmt_atoms (tb.(t_ops)) (tb.(t_muls)) (tb.(t_dms)) (tb.(t_rels)) true (tb.(t_st)) false c g; c)
      else gc0 in
    let catoms := if deep then tb.(t_cdeep) else tb.(t_catoms) in
    (* [comment removed for export] *)
    (match gc.(ats) with
     | _ :: _ => ()
     | [] =>
         let rec seed (i : int) (k : int) : unit :=
           if Int.lt i 0 then () else if Int.le k 0 then () else
             ((if (if logic then true else Bool.neg (Array.get (tb.(t_clogic)) i)) then
                 List.iter (fun a => if mem_int a (gc.(ats)) then () else gc.(ats) := a :: gc.(ats)) (Array.get catoms i)
               else ());
              seed (Int.sub i 1) (Int.sub k 1)) in
         seed (Int.sub (Array.length catoms) 1) 6
     end);
    let occ := Array.make (Int.add na 1) 0 in
    let alive := Array.make (Int.add nc 1) false in
    let rec init (i : int) : unit :=
      if Int.lt i nc then
        ((if (if logic then true else Bool.neg (Array.get (tb.(t_clogic)) i)) then
            (Array.set alive i true;
             List.iter (fun a => Array.set occ a (Int.add (Array.get occ a) 1)) (Array.get catoms i))
          else ());
         init (Int.add i 1))
      else () in
    init 0;
    List.iter (fun a => Array.set occ a (Int.add (Array.get occ a) 1000)) (gc.(ats));
    (* [comment removed for export] *)
    let changed := { contents := true } in
    let rec pend (i : int) : unit :=
      if Int.lt i nc then
        ((if (if Array.get alive i then (if deep then false else Array.get (tb.(t_csimple)) i) else false) then
            (let ats := Array.get catoms i in
             if exists_int (fun a => Int.equal (Array.get occ a) 1) ats then
               (Array.set alive i false;
                List.iter (fun a => Array.set occ a (Int.sub (Array.get occ a) 1)) ats;
                changed.(contents) := true)
             else ())
          else ());
         pend (Int.add i 1))
      else () in
    let rec pend_loop () : unit :=
      if changed.(contents) then (changed.(contents) := false; pend 0; pend_loop ()) else () in
    pend_loop ();
    (* [comment removed for export] *)
    let reach := Array.make (Int.add na 1) false in
    List.iter (fun a => Array.set reach a true) (gc.(ats));
    let creach := Array.make (Int.add nc 1) false in
    let rec bfs (i : int) : unit :=
      if Int.lt i nc then
        ((if (if Array.get alive i then Bool.neg (Array.get creach i) else false) then
            (let ats := Array.get catoms i in
             if exists_int (fun a => Array.get reach a) ats then
               (Array.set creach i true; List.iter (fun a => Array.set reach a true) ats; changed.(contents) := true)
             else ())
          else ());
         bfs (Int.add i 1))
      else () in
    let rec bfs_loop () : unit :=
      if changed.(contents) then (changed.(contents) := false; bfs 0; bfs_loop ()) else () in
    changed.(contents) := true; bfs_loop ();
    let keep := Array.make (Int.add nh 1) false in
    let rec mark (i : int) : unit :=
      if Int.lt i nc then ((if Array.get creach i then Array.set keep (Array.get (tb.(t_chyp)) i) true else ()); mark (Int.add i 1))
      else () in
    mark 0;
    (* [comment removed for export] *)
    let hs := Control.hyps () in
    let cur := List.fold_left (fun acc h => let (id, _, _) := h in FSet.add id acc) (FSet.empty FSet.Tags.ident_tag) hs in
    let dmk := { contents := deep } in
    let nlog := { contents := 0 } in
    let ids := { contents := List.filter (fun id => FSet.mem id cur) (tb.(t_others)) } in
    (* [comment removed for export] *)
    List.iter (fun h => let (id, body, ty) := h in
       if FSet.mem id (tb.(t_known)) then () else
       match body with
       | Some _ => ()
       | None => if (if zt_is_local id then zt_is_prop ty else false) then ids.(contents) := id :: ids.(contents) else ()
       end) hs;
    let rec coll (i : int) : unit :=
      if Int.lt i nh then
        ((if Array.get keep i then
            ((if Array.get (tb.(t_hevar)) i then Control.zero (Tactic_failure (Some (Message.of_string "diet: kept hypothesis with existential variables"))) else ());
             if Array.get (tb.(t_hlogic)) i then nlog.(contents) := Int.add (nlog.(contents)) 1 else ())
          else if Array.get (tb.(t_hclear)) i then
            (let id := Array.get (tb.(t_hid)) i in if FSet.mem id cur then ids.(contents) := id :: ids.(contents) else ())
          else ());
         coll (Int.add i 1))
      else () in
    coll 0;
    (* [comment removed for export] *)
    (if Int.gt (nlog.(contents)) max_logic then Control.zero (Tactic_failure (Some (Message.of_string "diet: too many logical hypotheses"))) else ());
    (match ids.(contents) with [] => () | _ :: _ => Std.clear (ids.(contents)) end);
    dmk.(contents).

  (* [comment removed for export] *)
  Ltac2 tier (tb : table) (logic : bool) : unit :=
    Control.enter (fun () =>
      if query tb logic then
        (* [comment removed for export] *)
        ltac1:(first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                     | Zify.zify; xlia zchecker ])
      else ltac1:(zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker)).
  (* [comment removed for export] *)
  Ltac2 tier_dm (tb : table) (logic : bool) : unit :=
    Control.enter (fun () =>
      let _ := query tb logic in
      ltac1:(Z.div_mod_to_equations; zify_noeuclid; xlia zchecker)).
  Ltac2 tiers_dm (tb : table) : unit :=
    Control.once (fun () => Control.plus (fun () => tier_dm tb false) (fun _ => tier_dm tb true)).
  Ltac2 dbg_fail (what : string) (e : exn) : unit :=
    if debug then
      (Message.print (Message.concat (Message.of_string what) (Message.of_exn e));
       Message.print (Message.concat (Message.of_string "  RL-GOAL: ") (Message.of_constr (Control.goal ()))))
    else ().
  Ltac2 tiers (tb : table) : unit :=
    Control.once (fun () =>
      Control.plus (fun () => tier tb false)
        (fun e1 => dbg_fail "RL-R1 failed: " e1;
                   Control.plus (fun () => tier tb true) (fun e2 => dbg_fail "RL-R2 failed: " e2; Control.zero e2))).

  (* [comment removed for export] *)
  Ltac2 with_side (sec : bool) (k : Ltac1.t) : unit :=
    Control.enter (fun () =>
      let tb := build sec in
      let side := Ltac1.lambda (fun _ => tiers tb; ltac1val:(idtac)) in
      Ltac1.apply k [side] Ltac1.run).
  Ltac2 with_side_loc (k : Ltac1.t) : unit := with_side false k.
  Ltac2 with_side_sec (k : Ltac1.t) : unit := with_side true k.
  Ltac2 with_side_flag (k : Ltac1.t) : unit := with_side sec k.
  (* [comment removed for export] *)
  Ltac2 oneshot (sec : bool) : unit := Control.enter (fun () => let tb := build sec in tiers tb).
  Ltac2 oneshot_loc () : unit := oneshot false.
  Ltac2 oneshot_sec () : unit := oneshot true.
  Ltac2 oneshot_flag () : unit := oneshot sec.
  Ltac2 oneshot_dm () : unit := Control.enter (fun () => let tb := build sec in tiers_dm tb).
  (* [comment removed for export] *)
  Ltac2 oneshot_mlia () : unit :=
    Control.enter (fun () =>
      let tb := build sec in
      Control.once (fun () =>
        Control.plus (fun () => tier tb false) (fun _ =>
        Control.plus (fun () => tier_dm tb false) (fun _ =>
        Control.plus (fun () => tier tb true) (fun _ => tier_dm tb true))))).
End RL.

(* [comment removed for export] *)
Ltac diet_with_side k := let f := ltac2:(k |- RL.with_side_flag k) in f k.
Ltac diet_with_side_loc k := let f := ltac2:(k |- RL.with_side_loc k) in f k.
(* [comment removed for export] *)
Ltac diet_nonstrict := ltac2:(RL.nonstrict ()).
Ltac diet_with_side_sec k := let f := ltac2:(k |- RL.with_side_sec k) in f k.
(* [comment removed for export] *)
Ltac diet_no_side := fun _ => fail.

Ltac rlia_tiers := ltac2:(RL.oneshot_flag ()).
Ltac rlia_loc_tiers := ltac2:(RL.oneshot_loc ()).
(* [comment removed for export] *)
Ltac rlia_dm_tiers := ltac2:(RL.oneshot_dm ()).
Ltac diet_mlia := first [ ltac2:(RL.oneshot_mlia ()) | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; nia ].
(* [comment removed for export] *)
Ltac diet_zmlia := first [ ltac2:(RL.oneshot_dm ()) | Z.div_mod_to_equations; lia ].
Ltac rlia_sec_tiers := ltac2:(RL.oneshot_sec ()).
Ltac rlia := first [ rlia_tiers | lia ].
Ltac rlia_sec := first [ rlia_sec_tiers | lia ].
Ltac rlia_top :=
  first [ rlia_tiers
        | zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Ltac rlia_sec_top :=
  first [ rlia_sec_tiers
        | zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Open Scope Z_scope.
Goal forall (f : Z -> Z) (a b c d e : Z) (P : Prop), (P -> a < b) -> a + 3 <= b -> b <= c -> d <= e -> e <= 7 -> (c <= 5 \/ a = 0) -> P -> a + 3 <= c.
Proof. intros. rlia_tiers. Qed.
Goal forall (a b c d e : Z), (a + 8 <= b \/ b + 16 <= a) -> 0 <= c <= 4 -> d = e -> (e < 0 \/ e > 5) -> (a + c + 1 <= b \/ b + 16 <= a + c).
Proof. intros. rlia_tiers. Qed.
Goal forall (a b : Z), 0 <= a -> a / 8 * 8 <= a.
Proof. intros. rlia_tiers. Qed.
Goal forall (x y z u v : Z) (l : list nat), x <= y -> y <= z -> z <= 10 -> u <= v -> Z.of_nat (length l) <= u -> x - 3 <= 10 /\ True.
Proof.
  intros. diet_with_side ltac:(fun side => split; [ first [ side tt | fail 100 "side failed" ] | exact I ]).
Qed.
Goal forall (x y : Z), x <= y -> False -> x = 5.
Proof. intros. Fail rlia_tiers. rlia. Qed.
