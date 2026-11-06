(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Ltac2 Require Import Ltac2 Printf.
From Ltac2 Require Constr FSet Fresh Env.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import LiaHints.
Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module Rec.
  Import Ltac2.
  Ltac2 mutable record : bool := false.
  Ltac2 mutable depth : int := 3.
  Ltac2 mutable lit_bits : int := 10.

  Ltac2 Type dctx := { c_xI : constructor; c_xO : constructor; c_xH : constructor; c_Zpos : constructor; c_Zneg : constructor; mutable h : int }.
  Ltac2 cof (r : Std.reference) : constructor := match r with Std.ConstructRef k => k | _ => Control.throw Not_found end.
  Ltac2 dmk () : dctx :=
    { c_xI := cof reference:(xI); c_xO := cof reference:(xO); c_xH := cof reference:(xH);
      c_Zpos := cof reference:(Zpos); c_Zneg := cof reference:(Zneg); h := 7 }.
  Ltac2 mix (x : dctx) (code : int) : unit := x.(h) := Int.lxor (Int.mul (x.(h)) 1000003) code.
  Ltac2 name_code (s : string) : int :=
    let n := String.length s in
    if Int.equal n 0 then 1 else
    Int.add (Char.to_int (String.get s (Int.sub n 1)))
      (Int.mul 128 (Int.add (Char.to_int (String.get s (Int.div n 2))) (Int.mul 128 (Int.add (Char.to_int (String.get s 0)) (Int.mul 128 n))))).
  Ltac2 rec pos_bits (x : dctx) (t : constr) (k : int) (w : int) (acc : int) : int :=
    if Int.le k 0 then Int.add acc (Int.mul w 3) else
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App hd a =>
        (match Constr.Unsafe.kind hd with
         | Constr.Unsafe.Constructor c _ =>
             if Constructor.equal c (x.(c_xI)) then pos_bits x (Array.get a 0) (Int.sub k 1) (Int.mul w 2) (Int.add acc w)
             else if Constructor.equal c (x.(c_xO)) then pos_bits x (Array.get a 0) (Int.sub k 1) (Int.mul w 2) acc
             else Int.add acc (Int.mul w 5)
         | _ => Int.add acc (Int.mul w 5)
         end)
    | Constr.Unsafe.Constructor c _ => if Constructor.equal c (x.(c_xH)) then Int.add acc w else Int.add acc (Int.mul w 7)
    | _ => Int.add acc (Int.mul w 7)
    end.
  Ltac2 rec walk (x : dctx) (d : int) (t : constr) : unit :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App hd args =>
        (match Constr.Unsafe.kind hd with
         | Constr.Unsafe.Constructor c _ =>
             if Constructor.equal c (x.(c_Zpos)) then mix x (Int.add 11 (Int.mul 16 (pos_bits x (Array.get args 0) lit_bits 1 0)))
             else if Constructor.equal c (x.(c_Zneg)) then mix x (Int.add 13 (Int.mul 16 (pos_bits x (Array.get args 0) lit_bits 1 0)))
             else (mix x 5; walk_args x d args)
         | Constr.Unsafe.Constant _ _ => mix x 2; walk_args x d args
         | Constr.Unsafe.Ind _ _ => mix x 59; walk_args x d args
         | Constr.Unsafe.Var id => mix x (Int.add 3 (name_code (Ident.to_string id))); walk_args x d args
         | _ => mix x 17; walk x d hd; walk_args x d args
         end)
    | Constr.Unsafe.Constant _ _ => mix x 61
    | Constr.Unsafe.Ind _ _ => mix x 67
    | Constr.Unsafe.Constructor _ _ => mix x 71
    | Constr.Unsafe.Var id => mix x (Int.add 3 (name_code (Ident.to_string id)))
    | Constr.Unsafe.Rel k => mix x (Int.add 19 (Int.mul 32 k))
    | Constr.Unsafe.Prod _ b => mix x 23; if Int.le d 0 then () else walk x (Int.sub d 1) b
    | Constr.Unsafe.Lambda _ _ => mix x 29
    | Constr.Unsafe.LetIn _ _ _ => mix x 31
    | Constr.Unsafe.Cast c _ _ => walk x d c
    | Constr.Unsafe.Sort _ => mix x 37
    | _ => mix x 41
    end
  with walk_args (x : dctx) (d : int) (args : constr array) : unit :=
    if Int.le d 0 then mix x 43 else (mix x 47; Array.iter (fun a => walk x (Int.sub d 1) a) args; mix x 53).
  Ltac2 dec (n : int) : string := Message.to_string (Message.of_int n).
  Ltac2 rec len_last (l : (ident * constr option * constr) list) (n : int) (last : ident option) : int * ident option :=
    match l with [] => (n, last) | hd :: r => let (id, _, _) := hd in len_last r (Int.add n 1) (Some id) end.
  Ltac2 digest_of (g : constr) (hyps : (ident * constr option * constr) list) : string :=
    let x := dmk () in
    walk x depth g;
    let (n, last) := len_last hyps 0 None in
    (match last with Some id => mix x (Int.add 97 (name_code (Ident.to_string id))) | None => () end);
    String.concat "." [dec (Int.land (x.(h)) 68719476735); dec n].
  Ltac2 digest () : string := digest_of (Control.goal ()) (Control.hyps ()).

  (* [comment removed for export] *)
  Ltac2 is_prop (ty : constr) : bool :=
    match Control.case (fun () => Constr.type ty) with
    | Val r => let (s, _) := r in (match Constr.Unsafe.kind s with Constr.Unsafe.Sort _ => Constr.equal s constr:(Prop) | _ => false end)
    | Err _ => false
    end.
  Ltac2 used_props (p : constr) (hyps : (ident * constr option * constr) list) : ident list :=
    let s := Fresh.Free.of_constr p in
    List.map_filter (fun h => let (id, body, ty) := h in
      if Ident.equal (Fresh.fresh s id) id then None
      else match body with
           | Some _ => None
           | None => if is_prop ty then Some id else None
           end) hyps.
  Ltac2 say (l : string list) : unit := Message.print (Message.of_string (String.concat " " ("LIAREC" :: l))).
  (* [comment removed for export] *)
  Ltac2 probe_term (ptac : Ltac1.t) : constr :=
    let g := Control.goal () in
    let r := { contents := None } in
    Ltac1.apply ltac1val:(fun g ptac => constr:(ltac:(ptac) : g)) [Ltac1.of_constr g; ptac] (fun v => r.(contents) := Ltac1.to_constr v);
    match r.(contents) with Some p => p | None => Control.zero (Tactic_failure None) end.
  Ltac2 on_fail (d : string option) : unit :=
    if record then say [(match d with Some d => d | None => digest () end); "F"] else ().
End Rec.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module Orc.
  Import Ltac2.
  Ltac2 mutable trace : bool := false.
  Ltac2 tr (m : string) (d : string) : unit := if trace then Message.print (Message.of_string (String.concat " " [m; d])) else ().

  Ltac2 mem_free (s : Fresh.Free.t) (u : ident) : bool := Bool.neg (Ident.equal (Fresh.fresh s u) u).
  Ltac2 fast_keep (ids : ident list) : unit :=
    let hyps := Control.hyps () in
    let hd := Env.instantiate reference:(True) in
    let tuple l := Constr.Unsafe.make (Constr.Unsafe.App hd (Array.of_list l)) in
    let of_hyp h := let (_, body, ty) := h in match body with Some b => tuple [b; ty] | None => ty end in
    let kept0 := List.fold_left (fun s id => FSet.add id s) (FSet.empty FSet.Tags.ident_tag) ids in
    let rec close (k : int) (kept : ident FSet.t) (frontier : constr list) :=
      if Int.le k 0 then kept else
      let fv := Fresh.Free.of_constr (tuple frontier) in
      let newl := List.map_filter (fun h => let (id, _, _) := h in
                    if FSet.mem id kept then None else if mem_free fv id then Some h else None) hyps in
      match newl with
      | [] => kept
      | _ :: _ => close (Int.sub k 1) (List.fold_left (fun s h => let (id, _, _) := h in FSet.add id s) kept newl) (List.map of_hyp newl)
      end in
    let seeds := Control.goal () :: List.map_filter (fun h => let (id, _, _) := h in if FSet.mem id kept0 then Some (of_hyp h) else None) hyps in
    let kept := close 16 kept0 seeds in
    let dead := List.map_filter (fun h => let (id, _, _) := h in if FSet.mem id kept then None else Some id) hyps in
    match dead with
    | [] => ()
    | _ :: _ => match Control.case (fun () => Std.clear dead) with
                | Val _ => ()
                | Err _ => Std.keep ids
                end
    end.
  Ltac2 keep_l1 (ns : Ltac1.t) : unit :=
    let l := match Ltac1.to_list ns with Some l => l | None => Control.throw Not_found end in
    fast_keep (List.map (fun v => match Ltac1.to_ident v with Some id => id | None => Control.throw Not_found end) l).

  (* [comment removed for export] *)
  Ltac2 run_none (d : string option) (knone : Ltac1.t) : unit :=
    if Rec.record then
      (let dg := match d with Some d => d | None => Rec.digest () end in
       let hyps := Control.hyps () in
       match Control.case (fun () => Control.time (Some "LC") (fun () => Rec.probe_term knone)) with
       | Val r => let (p, _) := r in
                  let ids := Rec.used_props p hyps in
                  Rec.say (dg :: "S" :: Rec.dec (List.length ids) :: List.map Ident.to_string ids);
                  Std.exact_no_check p
       | Err _ => Rec.say [dg; "F"]; Control.zero (Tactic_failure None)
       end)
    else
      match Control.case (fun () => Ltac1.run knone) with
      | Val _ => ()
      | Err _ => Control.zero (Tactic_failure None)
      end.

  Ltac2 dispatch (knone : Ltac1.t) (kkeep : Ltac1.t) : unit :=
    let t := LiaHints.tbl () in
    if Int.equal (String.length t) 0 then run_none None knone else
    if Constr.has_evar (Control.goal ()) then run_none None knone else
    let d := Rec.digest () in
    match LiaHints.lookup_in t d with
    | None => tr "ORCMISS" d; run_none (Some d) knone
    | Some (LiaHints.HFail) => tr "ORCFAIL" d; Control.zero (Tactic_failure None)
    | Some (LiaHints.HKeep names0) =>
        let names := match names0 with n :: r => if String.equal n "!X" then r else (if String.equal n "!R" then r else names0) | [] => [] end in
        let all := List.map_filter Ident.of_string names in
        let present := List.filter (fun id => match Control.case (fun () => Control.hyp id) with Val _ => true | Err _ => false end) all in
        let evar_in := List.exist (fun id => Constr.has_evar (Constr.type (Control.hyp id))) present in
        let usable := Bool.and (Bool.neg evar_in) (Bool.or (Int.equal (List.length all) 0) (Int.gt (List.length present) 0)) in
        if usable then
          (tr "ORCHIT" d;
           match Control.case (fun () => Ltac1.apply kkeep [Ltac1.of_list (List.map Ltac1.of_ident present)] Ltac1.run) with
           | Val _ => ()
           | Err _ => Rec.on_fail (Some d); Control.zero (Tactic_failure None)
           end)
        else (tr "ORCSTALE" d; run_none (Some d) knone)
    end.
End Orc.

Ltac lia_oracle_keep ns := let f := ltac2:(ns |- Ltac2.Control.enter (fun () => Orc.keep_l1 ns)) in f ns.
Ltac lia_oracle_dispatch knone kkeep := let f := ltac2:(knone kkeep |- Ltac2.Control.enter (fun () => Orc.dispatch knone kkeep)) in f knone kkeep.
