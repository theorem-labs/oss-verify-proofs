(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaTuning.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac2 lr_ops () : constr list :=
  [ '@Z.add; '@Z.sub; '@Z.mul; '@Z.opp; '@Z.succ; '@Z.pred; '@Z.div; '@Z.modulo; '@Z.quot; '@Z.rem; '@Z.max; '@Z.min; '@Z.abs;
    '@Z.of_nat; '@Z.to_nat; '@Z.le; '@Z.lt; '@Z.ge; '@Z.gt;
    '@Nat.add; '@Nat.sub; '@Nat.mul; '@Nat.max; '@Nat.min; '@Nat.pred; '@S; '@le; '@lt; '@ge; '@gt;
    '@eq; '@not; '@and; '@or; '@iff; '@Zpos; '@Zneg; '@xO; '@xI ].
Ltac2 lr_lits () : constr list := [ '@Z0; '@O; '@xH; '@True; '@False; 'Z; 'nat ].
Ltac2 lr_is_op (h : constr) : bool := List.exist (Constr.equal h) (lr_ops ()).
Ltac2 rec lr_is_lit (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App h args => if List.exist (Constr.equal h) ['@Zpos; '@Zneg; '@xO; '@xI; '@S] then Array.for_all lr_is_lit args else false
  | _ => List.exist (Constr.equal c) (lr_lits ())
  end.
Ltac2 Type lr_acc := { mutable lr_atoms : constr list }.
Ltac2 lr_add (a : lr_acc) (c : constr) : unit :=
  if List.exist (Constr.equal c) (a.(lr_atoms)) then () else a.(lr_atoms) := c :: a.(lr_atoms).
Ltac2 rec lr_scan (a : lr_acc) (c : constr) : unit :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App h args =>
      if Constr.equal h '@Z.pow then
        (if Bool.and (lr_is_lit (Array.get args 0)) (lr_is_lit (Array.get args 1)) then () else lr_add a c)
      else if lr_is_op h then Array.iter (lr_scan a) args
      else lr_add a c
  | Constr.Unsafe.Prod b body => lr_scan a (Constr.Binder.type b); (if Constr.Unsafe.closedn 0 body then lr_scan a body else ())
  | _ => if lr_is_lit c then () else lr_add a c
  end.
Ltac2 lr_atoms_of (c : constr) : constr list := let a := { lr_atoms := [] } in lr_scan a c; a.(lr_atoms).
Ltac2 lr_meets (xs : constr list) (ys : constr list) : bool := List.exist (fun x => List.exist (Constr.equal x) ys) xs.

(* [comment removed for export] *)
Ltac2 rec lr_arith (t : constr) : bool :=
  if zt_plain_arith t then true else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Constr.equal h '@or then (if lr_arith (Array.get args 0) then lr_arith (Array.get args 1) else false)
      else if Constr.equal h '@and then (if lr_arith (Array.get args 0) then lr_arith (Array.get args 1) else false)
      else if Constr.equal h '@not then lr_arith (Array.get args 0)
      else if Constr.equal h '@iff then (if lr_arith (Array.get args 0) then lr_arith (Array.get args 1) else false)
      else false
  | Constr.Unsafe.Prod b body =>
      if Constr.Unsafe.closedn 0 body then (if lr_arith (Constr.Binder.type b) then lr_arith body else false) else false
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 lr_prune_b (maxk : int) : bool :=
  let hs := Control.hyps () in
  let cands := List.map_filter (fun h => let (id, body, ty) := h in
                 match body with
                 | Some _ => None
                 | None => if lr_arith ty then Some (id, lr_atoms_of ty) else None
                 end) hs in
  let defs := List.map_filter (fun h => let (id, body, _) := h in
                 match body with Some b => Some (Control.hyp id, lr_atoms_of b) | None => None end) hs in
  let r := { lr_atoms := lr_atoms_of (Control.goal ()) } in
  let kept := { lr_atoms := [] } in
  let changed := { lr_atoms := ['I] } in
  let rec loop () :=
    match changed.(lr_atoms) with
    | [] => ()
    | _ :: _ =>
      changed.(lr_atoms) := [];
      List.iter (fun d => let (x, ats) := d in
        if List.exist (Constr.equal x) (r.(lr_atoms)) then
          List.iter (fun atm => if List.exist (Constr.equal atm) (r.(lr_atoms)) then () else (r.(lr_atoms) := atm :: r.(lr_atoms); changed.(lr_atoms) := ['I])) ats
        else ()) defs;
      List.iter (fun c => let (h, ats) := c in
        let hc := Control.hyp h in
        if List.exist (Constr.equal hc) (kept.(lr_atoms)) then ()
        else if lr_meets ats (r.(lr_atoms)) then
          (kept.(lr_atoms) := hc :: kept.(lr_atoms);
           List.iter (fun atm => if List.exist (Constr.equal atm) (r.(lr_atoms)) then () else r.(lr_atoms) := atm :: r.(lr_atoms)) ats;
           changed.(lr_atoms) := ['I])
        else ()) cands;
      loop ()
    end in
  loop ();
  let complete := List.for_all (fun c => let (h, _) := c in List.exist (Constr.equal (Control.hyp h)) (kept.(lr_atoms))) cands in
  (* [comment removed for export] *)
  (if Int.gt (Int.mul 100 (List.length (kept.(lr_atoms)))) (Int.mul maxk (List.length cands)) then Control.zero (Tactic_failure None) else ());
  let drop := List.map_filter (fun h => let (id, body, ty) := h in
                 match body with
                 | Some _ => None
                 | None => if List.exist (Constr.equal (Control.hyp id)) (kept.(lr_atoms)) then None else if zt_is_prop ty then Some id else None
                 end) hs in
  Control.plus (fun () => Std.clear drop)
    (fun _ => List.iter (fun id => Control.plus (fun () => Std.clear [id]) (fun _ => ())) drop);
  (* [comment removed for export] *)
  let ddefs := List.map_filter (fun h => let (id, body, _) := h in
                 match body with
                 | Some _ => if List.exist (Constr.equal (Control.hyp id)) (r.(lr_atoms)) then None else Some id
                 | None => None
                 end) (List.rev (Control.hyps ())) in
  List.iter (fun id => Control.plus (fun () => Std.clear [id]) (fun _ => ())) ddefs;
  complete.
(* [comment removed for export] *)
Ltac2 lr_prune_hub (k : int) : unit :=
  let hs := Control.hyps () in
  let cands := List.map_filter (fun h => let (id, body, ty) := h in
                 match body with
                 | Some _ => None
                 | None => if lr_arith ty then Some (id, lr_atoms_of ty) else None
                 end) hs in
  let defs := List.map_filter (fun h => let (id, body, _) := h in
                 match body with Some b => Some (Control.hyp id, lr_atoms_of b) | None => None end) hs in
  let count (a : constr) : int := List.fold_left (fun n c => let (_, ats) := c in if List.exist (Constr.equal a) ats then Int.add n 1 else n) 0 cands in
  let hub := { lr_atoms := [] } in
  let nonhub := { lr_atoms := [] } in
  let is_hub (a : constr) : bool :=
    if List.exist (Constr.equal a) (hub.(lr_atoms)) then true
    else if List.exist (Constr.equal a) (nonhub.(lr_atoms)) then false
    else if Int.gt (count a) k then (hub.(lr_atoms) := a :: hub.(lr_atoms); true) else (nonhub.(lr_atoms) := a :: nonhub.(lr_atoms); false) in
  (* [comment removed for export] *)
  let r := { lr_atoms := List.filter (fun a => Bool.neg (is_hub a)) (lr_atoms_of (Control.goal ())) } in
  let kept := { lr_atoms := [] } in
  let changed := { lr_atoms := ['I] } in
  let add_atoms (ats : constr list) :=
    List.iter (fun atm => if List.exist (Constr.equal atm) (r.(lr_atoms)) then () else if is_hub atm then () else (r.(lr_atoms) := atm :: r.(lr_atoms); changed.(lr_atoms) := ['I])) ats in
  let rec loop () :=
    match changed.(lr_atoms) with
    | [] => ()
    | _ :: _ =>
      changed.(lr_atoms) := [];
      List.iter (fun d => let (x, ats) := d in if List.exist (Constr.equal x) (r.(lr_atoms)) then add_atoms ats else ()) defs;
      List.iter (fun c => let (h, ats) := c in
        let hc := Control.hyp h in
        if List.exist (Constr.equal hc) (kept.(lr_atoms)) then ()
        else if lr_meets ats (r.(lr_atoms)) then (kept.(lr_atoms) := hc :: kept.(lr_atoms); changed.(lr_atoms) := ['I]; add_atoms ats)
        else ()) cands;
      loop ()
    end in
  loop ();
  let drop := List.map_filter (fun h => let (id, body, ty) := h in
                 match body with
                 | Some _ => None
                 | None => if List.exist (Constr.equal (Control.hyp id)) (kept.(lr_atoms)) then None else if zt_is_prop ty then Some id else None
                 end) hs in
  Control.plus (fun () => Std.clear drop)
    (fun _ => List.iter (fun id => Control.plus (fun () => Std.clear [id]) (fun _ => ())) drop);
  let ddefs := List.map_filter (fun h => let (id, body, _) := h in
                 match body with
                 | Some _ => if List.exist (Constr.equal (Control.hyp id)) (r.(lr_atoms)) then None else Some id
                 | None => None
                 end) (List.rev (Control.hyps ())) in
  List.iter (fun id => Control.plus (fun () => Std.clear [id]) (fun _ => ())) ddefs.

Ltac2 lr_prune () : unit := let _ := lr_prune_b 100 in ().

(* [comment removed for export] *)
Ltac2 lr_goal_atoms () : constr list :=
  let hs := Control.hyps () in
  let defs := List.map_filter (fun h => let (id, body, _) := h in
                 match body with Some b => Some (Control.hyp id, lr_atoms_of b) | None => None end) hs in
  let g := { lr_atoms := lr_atoms_of (Control.goal ()) } in
  let ch := { lr_atoms := ['I] } in
  let rec loop () :=
    match ch.(lr_atoms) with
    | [] => ()
    | _ :: _ =>
      ch.(lr_atoms) := [];
      List.iter (fun d => let (x, ats) := d in
        if List.exist (Constr.equal x) (g.(lr_atoms)) then
          List.iter (fun atm => if List.exist (Constr.equal atm) (g.(lr_atoms)) then () else (g.(lr_atoms) := atm :: g.(lr_atoms); ch.(lr_atoms) := ['I])) ats
        else ()) defs;
      loop ()
    end in
  loop (); g.(lr_atoms).
Ltac2 lr_prune_sub () : unit :=
  let g := lr_goal_atoms () in
  let hs := Control.hyps () in
  let drop := List.map_filter (fun h => let (id, body, ty) := h in
                 match body with
                 | Some _ => None
                 | None => if zt_is_prop ty then
                             (if lr_arith ty then (if List.for_all (fun a => List.exist (Constr.equal a) g) (lr_atoms_of ty) then None else Some id) else Some id)
                           else None
                 end) hs in
  Control.plus (fun () => Std.clear drop)
    (fun _ => List.iter (fun id => Control.plus (fun () => Std.clear [id]) (fun _ => ())) drop);
  let ddefs := List.map_filter (fun h => let (id, body, _) := h in
                 match body with
                 | Some _ => if List.exist (Constr.equal (Control.hyp id)) g then None else Some id
                 | None => None
                 end) (List.rev (Control.hyps ())) in
  List.iter (fun id => Control.plus (fun () => Std.clear [id]) (fun _ => ())) ddefs.

Ltac lia_tiers := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                        | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
Ltac2 lr_tiers () : unit := ltac1:(lia_tiers).
(* [comment removed for export] *)
Ltac2 lr_bc () : unit :=
  let st := { lr_atoms := [] } in
  let big := { lr_atoms := [] } in
  Control.plus (fun () => let complete := Control.once (fun () => Control.plus (fun () => lr_prune_b 101) (fun e => big.(lr_atoms) := ['I]; Control.zero e)) in
                          (if complete then st.(lr_atoms) := ['I] else ()); lr_tiers ())
    (fun e => match big.(lr_atoms) with
              | _ :: _ => lr_tiers ()          (* [comment removed for export] *)
              | [] => match st.(lr_atoms) with [] => ltac1:(Zify.zify; xlia zchecker) | _ :: _ => Control.zero e end
              end).
(* [comment removed for export] *)
Ltac plia := first [ once ltac2:(lr_prune_sub ()); lia_tiers | once ltac2:(lr_prune_hub 5); lia_tiers | ltac2:(lr_bc ()) ].
Ltac plia_b := plia.
(* [comment removed for export] *)
Ltac plia_a := first [ once ltac2:(lr_prune_sub ()); lia_tiers | lia_tiers ].
(* [comment removed for export] *)
Ltac plia_cheap := first [ once ltac2:(lr_prune_sub ()); lia_tiers | once ltac2:(lr_prune_hub 5); lia_tiers ].
(* [comment removed for export] *)
Ltac plia_seed1 H := revert H; plia.
