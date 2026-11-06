(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module KV.
  Ltac2 rec vars_of (c : constr) (acc : ident list) : ident list :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.Var id => if List.exist (Ident.equal id) acc then acc else id :: acc
    | Constr.Unsafe.App f args => Array.fold_left (fun a y => vars_of y a) (vars_of f acc) args
    | Constr.Unsafe.Cast y _ _ => vars_of y acc
    | Constr.Unsafe.Proj _ _ y => vars_of y acc
    | _ => acc
    end.
  Ltac2 mentions (vs : ident list) (c : constr) : bool :=
    if Constr.Unsafe.closedn 0 (Constr.Unsafe.closenl vs 1 c) then false else true.
  Ltac2 is_local (id : ident) : bool := match Env.get [id] with None => true | Some _ => false end.
  Ltac2 heads () : Std.reference list :=
    [reference:(eq); reference:(and); reference:(or); reference:(not); reference:(iff); reference:(le); reference:(lt); reference:(ge); reference:(gt);
     reference:(Z.le); reference:(Z.lt); reference:(Z.ge); reference:(Z.gt); reference:(N.le); reference:(N.lt); reference:(Z.divide)].
  Ltac2 rec is_ref (h : constr) (l : Std.reference list) : bool :=
    match l with
    | [] => false
    | r :: t =>
        (match r, Constr.Unsafe.kind h with
         | Std.ConstRef c, Constr.Unsafe.Constant c' _ => if Constant.equal c c' then true else is_ref h t
         | Std.IndRef i, Constr.Unsafe.Ind i' _ => if Ind.equal i i' then true else is_ref h t
         | _, _ => is_ref h t
         end)
    end.
  Ltac2 arith_head (hs : Std.reference list) (ty : constr) : bool :=
    match Constr.Unsafe.kind ty with
    | Constr.Unsafe.App h _ => is_ref h hs
    | _ => false
    end.
  Ltac2 keep_vars (cs : constr list) : unit :=
    let vs := List.fold_left (fun a c => vars_of c a) [] cs in
    match vs with
    | [] => ()
    | _ :: _ =>
        let hs := heads () in
        let ids := List.map_filter (fun h => let (id, body, ty) := h in
                      match body with
                      | Some _ => None
                      | None => if arith_head hs ty then (if mentions vs ty then None else if is_local id then Some id else None) else None
                      end) (Control.hyps ()) in
        match ids with [] => () | _ :: _ => Std.clear ids end
    end.
End KV.
Ltac keep_vars1 t := let f := ltac2:(t |- Control.enter (fun () => KV.keep_vars [Option.get (Ltac1.to_constr t)])) in f t.
(* [comment removed for export] *)

(* [comment removed for export] *)
Goal forall (l : list nat) (x y z : Z), (0 <= x)%Z -> (y < z)%Z -> Z.of_nat (length l) = 5%Z -> (x <= y)%Z -> Z.of_nat (length (List.firstn 2 l)) = 2%Z.
Proof.
  intros l x y z H1 H2 H3 H4. rewrite List.length_firstn. keep_vars1 l.
  lazymatch goal with _ : (0 <= x)%Z |- _ => fail "not cleared" | _ => idtac end.
  lazymatch goal with _ : Z.of_nat (length l) = 5%Z |- _ => idtac end. Lia.lia.
Qed.
