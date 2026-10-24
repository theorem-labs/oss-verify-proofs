(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Zify.
From Ltac2 Require Import Ltac2.
#[global] Set Default Proof Mode "Classic".

Ltac2 rec zon_nat_lit (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      if Int.equal (Array.length args) 1 then
        (if Constr.equal f 'S then zon_nat_lit (Array.get args 0) else false)
      else false
  | _ => Constr.equal t 'O
  end.
Ltac2 zon_mem (t : constr) (l : constr list) : bool := List.exist (fun u => Constr.equal t u) l.
Ltac2 rec zon_collect (t : constr) (acc : constr list) : constr list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      if Bool.and (Int.equal (Array.length args) 1) (Constr.equal f 'Z.of_nat) then
        (if zon_nat_lit (Array.get args 0) then (if zon_mem t acc then acc else t :: acc) else zon_collect (Array.get args 0) acc)
      else Array.fold_left (fun a x => zon_collect x a) (zon_collect f acc) args
  | Constr.Unsafe.Prod b c => zon_collect c (zon_collect (Constr.Binder.type b) acc)
  | Constr.Unsafe.Cast c _ _ => zon_collect c acc
  | _ => acc
  end.
Ltac2 rec zon_count (t : constr) (acc : int) : int :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App _ args => zon_count (Array.get args 0) (Int.add acc 1)
  | _ => acc
  end.
Ltac2 rec zon_pos (n : int) : constr :=
  if Int.equal n 1 then 'xH else
  let h := zon_pos (Int.div n 2) in
  if Int.equal (Int.mod n 2) 0 then constr:(xO $h) else constr:(xI $h).
Ltac2 zon_z (n : int) : constr := if Int.equal n 0 then 'Z0 else let p := zon_pos n in constr:(Zpos $p).
Ltac2 zon_hook () : unit :=
  Control.enter (fun () =>
    let l := zon_collect (Control.goal ()) [] in
    List.iter (fun c =>
      let k := match Constr.Unsafe.kind c with Constr.Unsafe.App _ args => Array.get args 0 | _ => c end in
      let z := zon_z (zon_count k 0) in
      ltac1:(c z |- change c with z) (Ltac1.of_constr c) (Ltac1.of_constr z)) l).
(* [comment removed for export] *)
Ltac zon_hook := lazymatch goal with |- context [Z.of_nat _] => ltac2:(zon_hook ()) | |- _ => idtac end.

(* [comment removed for export] *)
Ltac Zify.zify_pre_hook ::= zon_hook.
