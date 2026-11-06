(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2 Constr.
From Ltac2 Require Ltac1 Array Int Option List Env Control Bool.

(* [comment removed for export] *)
Ltac2 rec dle (c : constr) : constr :=
  match Unsafe.kind c with
  | Unsafe.LetIn b v body =>
      let body' := dle body in
      if Unsafe.noccurn 1 body' then Unsafe.substnl [v] 0 body'
      else Unsafe.make (Unsafe.LetIn b v body')
  | Unsafe.App f args =>
      let k := Int.sub (Array.length args) 1 in
      let last := Array.get args k in
      let go () := let a := Array.copy args in Array.set a k (dle last); Unsafe.make (Unsafe.App f a) in
      (match Unsafe.kind last with
       | Unsafe.LetIn _ _ _ => go ()
       | Unsafe.App _ _ => go ()
       | Unsafe.Cast _ _ _ => go ()
       | Unsafe.Lambda _ _ => go ()
       | _ => c
       end)
  | Unsafe.Lambda b body => Unsafe.make (Unsafe.Lambda b (dle body))
  | Unsafe.Cast c k t => Unsafe.make (Unsafe.Cast (dle c) k t)
  | _ => c
  end.
Ltac2 dle_strip_cast (c : constr) : constr := match Unsafe.kind c with Unsafe.Cast c _ _ => c | _ => c end.
Ltac2 dle_var_occurs (id : ident) (c : constr) : bool := Bool.neg (Unsafe.noccurn 1 (Unsafe.closenl [id] 1 c)).
(* [comment removed for export] *)
Ltac2 dle_keep_section (p : constr) (p' : constr) : constr :=
  List.fold_left (fun acc h =>
    let (id, _, ty) := h in
    match Env.get [id] with
    | None => acc
    | Some _ =>
        if dle_var_occurs id acc then acc
        else if dle_var_occurs id p then
          Unsafe.make (Unsafe.LetIn (Binder.make None ty) (Unsafe.make (Unsafe.Var id)) (Unsafe.liftn 1 1 acc))
        else acc
    end) p' (Control.hyps ()).
Ltac2 dle_main (p : constr) : constr := let p0 := dle_strip_cast p in dle_keep_section p0 (dle p0).
#[global] Set Default Proof Mode "Classic".
Ltac dle_exact p := let f := ltac2:(p |- let c := Option.get (Ltac1.to_constr p) in let c' := dle_main c in ltac1:(c |- exact_no_check c) (Ltac1.of_constr c')) in f p.
(* [comment removed for export] *)
Ltac dle_wrap tac :=
  idtac;   (* [comment removed for export] *)
  let G := lazymatch goal with |- ?G => G end in
  tryif has_evar G then tac
  else (let p := constr:(ltac:(tac) : G) in dle_exact p).
