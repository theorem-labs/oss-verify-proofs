(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify.
From Ltac2 Require Import Ltac2.
From Ltac2 Require FSet FMap Constant Ind Ltac1.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac2 rec lf_split_free (rels : constant FSet.t) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant c _ => FSet.mem c rels
      | Constr.Unsafe.Ind i _ =>
          if Ind.equal i (lf_ind reference:(and)) then
            (if lf_split_free rels (Array.get args 0) then lf_split_free rels (Array.get args 1) else false)
          else if Ind.equal i (lf_ind reference:(eq)) then true
          else Ind.equal i (lf_ind reference:(Peano.le))
      | _ => false
      end
  | Constr.Unsafe.Ind _ _ => true
  | _ => false
  end.

Ltac2 lf_cap () : int := 3.

Ltac2 lf_fail () : unit := Control.zero (Tactic_failure None).
Ltac2 lf_succeeds (t : unit -> unit) : bool :=
  match Control.case t with Val _ => true | Err _ => false end.

(* [comment removed for export] *)
Ltac2 rec lf_vars_dc (t : constr) (lo : int) (len : int) (acc : int list) : int list :=
  if Int.equal len 1 then lo :: acc
  else
    let h := Int.div len 2 in
    let lo2 := Int.add lo h in
    let len2 := Int.sub len h in
    if Constr.Unsafe.noccur_between lo h t then lf_vars_dc t lo2 len2 acc
    else
      let acc := lf_vars_dc t lo h acc in
      if Constr.Unsafe.noccur_between lo2 len2 t then acc else lf_vars_dc t lo2 len2 acc.
(* [comment removed for export] *)
Ltac2 lf_vars (n : int) (t : constr) : int list :=
  if Int.le n 0 then [] else if Constr.Unsafe.noccur_between 1 n t then [] else lf_vars_dc t 1 n [].
Ltac2 lf_plan2F (st : lf_state) (hit1 : (ident * constr) list) (miss1 : (ident * constr) list) : (ident * constr) list option :=
  let n := st.(st_n) in
  let inv := st.(st_inv) in
  let take_new (vs : int list) (acc : int list) : int list :=
    List.fold_left (fun a j => if Array.get inv j then a else (Array.set inv j true; j :: a)) acc vs in
  let rec expand (news : int list) (acc : int list) : int list :=
    match news with
    | [] => acc
    | i :: r =>
        match Array.get (st.(st_bodies)) (Int.sub i 1) with
        | None => expand r (i :: acc)
        | Some b => expand (take_new (lf_vars n (Constr.Unsafe.closenl (st.(st_xs)) 1 b)) r) (i :: acc)
        end
    end in
  let rec closure (hitsv : int list list) (kept : (ident * constr) list) (rest : ((ident * constr) * int list) list) (grown : bool) :=
    match hitsv with
    | [] => (kept, grown)
    | _ :: _ =>
        match rest with
        | [] => (kept, grown)
        | _ :: _ =>
            let news := expand (List.fold_left (fun a vs => take_new vs a) [] hitsv) [] in
            match news with
            | [] => (kept, grown)
            | _ :: _ =>
                let (h, m) := List.partition (fun q => let (_, vs) := q in List.exist (fun j => Array.get inv j) vs) rest in
                match h with
                | [] => (kept, grown)
                | _ :: _ =>
                    closure (List.map (fun q => let (_, vs) := q in vs) h)
                            (List.append (List.map (fun q => let (p, _) := q in p) h) kept) m true
                end
            end
        end
    end in
  match hit1 with
  | [] => None
  | _ :: _ =>
      match miss1 with
      | [] => None
      | _ :: _ =>
          let hitsv := List.map (fun p => let (_, t') := p in lf_vars n t') hit1 in
          let rest := List.map (fun p => let (_, t') := p in (p, lf_vars n t')) miss1 in
          let (kept, grown) := closure hitsv hit1 rest false in
          if grown then Some kept else None
      end
  end.
Ltac2 lf_cap_main (t1 : unit -> unit) (doomed : unit -> unit) : unit :=
  let g := Control.goal () in
  let old () := Control.plus (fun () => ltac1:(LiaFast.lia_fast_tiers)) (fun _ => t1 ()) in
  match Constr.Unsafe.kind g with
  | Constr.Unsafe.Prod _ _ => old ()
  | _ =>
    let rels := lf_rel_consts () in
    if Bool.neg (lf_arith_shape rels g) then t1 () else
    match Control.case (fun () => lf_plan1 ()) with
    | Err _ => t1 ()
    | Val v =>
        let (r, _) := v in
        let (st, hit1, miss1) := r in
        let nsplit := fun (l : (ident * constr) list) =>
          List.length (List.filter (fun p => let (_, t') := p in Bool.neg (lf_split_free rels t')) l) in
        let cap := lf_cap () in
        let run (l : (ident * constr) list) : unit := lf_keep l; ltac1:(lf_close) in
        (* [comment removed for export] *)
        let t1_or_doomed () : unit := if lf_succeeds doomed then lf_fail () else t1 () in
        if Int.le (nsplit hit1) cap then
          Control.plus (fun () => run hit1)
            (fun _ =>
               match lf_plan2F st hit1 miss1 with
               | None => t1_or_doomed ()
               | Some kept =>
                   if Int.le (nsplit kept) cap then Control.plus (fun () => run kept) (fun _ => t1_or_doomed ())
                   else Control.plus t1 (fun _ => run kept)
               end)
        else
          Control.plus t1
            (fun _ => Control.plus (fun () => run hit1)
               (fun _ => match lf_plan2F st hit1 miss1 with Some kept => run kept | None => lf_fail () end))
    end
  end.
(* [comment removed for export] *)
Ltac lia_cap t1 dm :=
  solve [ let f := ltac2:(a b |- Control.enter (fun () => Control.once (fun () => lf_cap_main (fun () => Ltac1.run a) (fun () => Ltac1.run b)))) in f t1 dm ].

(* [comment removed for export] *)
Ltac2 lf_cap_main_s (t1 : unit -> unit) (doomed : unit -> unit) : unit :=
  let g := Control.goal () in
  let old () := Control.plus (fun () => ltac1:(LiaFast.lia_fast_tiers)) (fun _ => t1 ()) in
  match Constr.Unsafe.kind g with
  | Constr.Unsafe.Prod _ _ => old ()
  | _ =>
    let rels := lf_rel_consts () in
    if Bool.neg (lf_arith_shape rels g) then t1 () else
    match Control.case (fun () => lf_plan1 ()) with
    | Err _ => t1 ()
    | Val v =>
        let (r, _) := v in
        let (st, hit1, miss1) := r in
        let nsplit := fun (l : (ident * constr) list) =>
          List.length (List.filter (fun p => let (_, t') := p in Bool.neg (lf_split_free rels t')) l) in
        let cap := lf_cap () in
        let run (l : (ident * constr) list) : unit := lf_keep l; ltac1:(lf_close) in
        (* [comment removed for export] *)
        let t1_or_doomed () : unit := lf_fail () in      (* [comment removed for export] *)
        if Int.le (nsplit hit1) cap then
          Control.plus (fun () => run hit1)
            (fun _ =>
               match lf_plan2F st hit1 miss1 with
               | None => t1_or_doomed ()
               | Some kept =>
                   if Int.le (nsplit kept) cap then Control.plus (fun () => run kept) (fun _ => t1_or_doomed ())
                   else Control.plus t1 (fun _ => run kept)
               end)
        else
          Control.plus t1
            (fun _ => Control.plus (fun () => run hit1)
               (fun _ => match lf_plan2F st hit1 miss1 with Some kept => run kept | None => lf_fail () end))
    end
  end.
Ltac lia_cap_s t1 dm :=
  solve [ let f := ltac2:(a b |- Control.enter (fun () => Control.once (fun () => lf_cap_main_s (fun () => Ltac1.run a) (fun () => Ltac1.run b)))) in f t1 dm ].
