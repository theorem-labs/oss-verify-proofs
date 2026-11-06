(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From Stdlib Require ZArith Lia Zify. From Stdlib Require List. From Ltac2 Require Ltac2. From Ltac2 Require Constr Control List Std Env Array Int Fresh Ident.
Module L5FastLia.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Zify.
From Stdlib Require List.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Control List Std Env Array Int Fresh Ident. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac2 rec has_arith_ref (t : constr) : bool :=
  lazy_match! t with
  | @eq ?ty _ _ => lazy_match! ty with Z => true | nat => true | positive => true | N => true | _ => false end
  | Z.le _ _ => true | Z.lt _ _ => true | Z.ge _ _ => true | Z.gt _ _ => true
  | le _ _ => true | lt _ _ => true | ge _ _ => true | gt _ _ => true
  | N.le _ _ => true | N.lt _ _ => true | Pos.le _ _ => true | Pos.lt _ _ => true | Z.divide _ _ => true
  | False => true
  | ?a /\ ?b => if has_arith_ref a then true else has_arith_ref b
  | ?a \/ ?b => if has_arith_ref a then true else has_arith_ref b
  | ?a <-> ?b => if has_arith_ref a then true else has_arith_ref b
  | ~ ?a => has_arith_ref a
  | ?a -> ?b => if has_arith_ref a then true else has_arith_ref b
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 rec atomic_arith_ref (t : constr) : bool :=
  lazy_match! t with
  | ?a /\ ?b => if atomic_arith_ref a then atomic_arith_ref b else false
  | @eq ?ty _ _ => lazy_match! ty with Z => true | nat => true | positive => true | N => true | _ => false end
  | Z.le _ _ => true | Z.lt _ _ => true | Z.ge _ _ => true | Z.gt _ _ => true
  | le _ _ => true | lt _ _ => true | ge _ _ => true | gt _ _ => true
  | False => true
  | _ => false
  end.
Ltac2 has_hard (t : constr) : bool :=
  match! t with
  | context [Z.modulo _ _] => true
  | context [Z.div _ _] => true
  | context [Z.pow _ ?e] => lazy_match! e with Zpos _ => Control.zero Match_failure | Z0 => Control.zero Match_failure | _ => true end
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 Type ktab := {
  k_eq : constr; k_and : constr; k_or : constr; k_le : constr; k_False : constr;
  k_Z : constr; k_nat : constr; k_positive : constr; k_N : constr;
  k_iff : constr; k_not : constr;
  k_ord : constr list;   (* [comment removed for export] *)
  k_ordx : constr list   (* [comment removed for export] *)
}.
Ltac2 mk_ktab () : ktab := {
  k_eq := Env.instantiate reference:(eq); k_and := Env.instantiate reference:(and); k_or := Env.instantiate reference:(or);
  k_le := Env.instantiate reference:(le); k_False := Env.instantiate reference:(False);
  k_Z := Env.instantiate reference:(Z); k_nat := Env.instantiate reference:(nat); k_positive := Env.instantiate reference:(positive);
  k_N := Env.instantiate reference:(N);
  k_iff := Env.instantiate reference:(iff); k_not := Env.instantiate reference:(not);
  k_ord := [Env.instantiate reference:(Z.le); Env.instantiate reference:(Z.lt); Env.instantiate reference:(Z.ge); Env.instantiate reference:(Z.gt);
            Env.instantiate reference:(lt); Env.instantiate reference:(ge); Env.instantiate reference:(gt)];
  k_ordx := [Env.instantiate reference:(N.le); Env.instantiate reference:(N.lt); Env.instantiate reference:(Pos.le); Env.instantiate reference:(Pos.lt);
             Env.instantiate reference:(Z.divide)]
}.
Ltac2 rec uncast (c : constr) : constr := match Constr.Unsafe.kind c with Constr.Unsafe.Cast c _ _ => uncast c | _ => c end.
Ltac2 rec mem_c (h : constr) (l : constr list) : bool := match l with [] => false | x :: l => if Constr.equal h x then true else mem_c h l end.
Ltac2 arith_ty (k : ktab) (ty : constr) : bool :=
  let ty := uncast ty in
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.Ind _ _ =>
      if Constr.equal ty (k.(k_Z)) then true else if Constr.equal ty (k.(k_nat)) then true
      else if Constr.equal ty (k.(k_positive)) then true else Constr.equal ty (k.(k_N))
  | _ => false
  end.
Ltac2 rec has_arith_k (k : ktab) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      let f := uncast f in
      let n := Array.length args in
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Ind _ _ =>
          if Constr.equal f (k.(k_eq)) then (if Int.equal n 3 then arith_ty k (Array.get args 0) else false)
          else if Int.equal n 2 then
            (if Constr.equal f (k.(k_and)) then (if has_arith_k k (Array.get args 0) then true else has_arith_k k (Array.get args 1))
             else if Constr.equal f (k.(k_or)) then (if has_arith_k k (Array.get args 0) then true else has_arith_k k (Array.get args 1))
             else Constr.equal f (k.(k_le)))
          else false
      | Constr.Unsafe.Constant _ _ =>
          if Int.equal n 2 then
            (if mem_c f (k.(k_ord)) then true
             else if Constr.equal f (k.(k_iff)) then (if has_arith_k k (Array.get args 0) then true else has_arith_k k (Array.get args 1))
             else mem_c f (k.(k_ordx)))
          else if Int.equal n 1 then (if Constr.equal f (k.(k_not)) then has_arith_k k (Array.get args 0) else false)
          else false
      | _ => false
      end
  | Constr.Unsafe.Prod b body =>
      if Constr.Unsafe.noccurn 1 body then (if has_arith_k k (Constr.Binder.type b) then true else has_arith_k k body) else false
  | Constr.Unsafe.Ind _ _ => Constr.equal t (k.(k_False))
  | Constr.Unsafe.Cast c _ _ => has_arith_k k c
  | _ => false
  end.
Ltac2 rec atomic_arith_k (k : ktab) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      let f := uncast f in
      let n := Array.length args in
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Ind _ _ =>
          if Constr.equal f (k.(k_eq)) then (if Int.equal n 3 then arith_ty k (Array.get args 0) else false)
          else if Int.equal n 2 then
            (if Constr.equal f (k.(k_and)) then (if atomic_arith_k k (Array.get args 0) then atomic_arith_k k (Array.get args 1) else false)
             else Constr.equal f (k.(k_le)))
          else false
      | Constr.Unsafe.Constant _ _ => if Int.equal n 2 then mem_c f (k.(k_ord)) else false
      | _ => false
      end
  | Constr.Unsafe.Ind _ _ => Constr.equal t (k.(k_False))
  | Constr.Unsafe.Cast c _ _ => atomic_arith_k k c
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 has_arith (t : constr) : bool := has_arith_k (mk_ktab ()) t.
Ltac2 atomic_arith (t : constr) : bool := atomic_arith_k (mk_ktab ()) t.

(* [comment removed for export] *)
Ltac2 in_free (id : ident) (s : Fresh.Free.t) : bool := if Ident.equal (Fresh.fresh s id) id then false else true.
(* [comment removed for export] *)
Ltac2 fresh_is_plain () : bool := Ident.equal (Fresh.fresh Fresh.Free.empty @fitl_probe) @fitl_probe.
Ltac2 free_of_list (h : constr) (l : constr list) : Fresh.Free.t :=
  match l with
  | [] => Fresh.Free.empty
  | [t] => Fresh.Free.of_constr t
  | _ => Fresh.Free.of_constr (Constr.Unsafe.make (Constr.Unsafe.App h (Array.of_list l)))
  end.
Ltac2 decl_terms (body : constr option) (ty : constr) (acc : constr list) : constr list :=
  match body with Some b => b :: ty :: acc | None => ty :: acc end.
(* [comment removed for export] *)
Ltac2 rec keep_scan (s0 : Fresh.Free.t) (hyps : (ident * constr option * constr) list) (flags : bool list) : ident list * ident list * Fresh.Free.t :=
  match hyps with
  | [] => ([], [], s0)
  | h :: hyps =>
      let (id, body, ty) := h in
      let (fl, flags) := match flags with f :: r => (f, r) | [] => (false, []) end in
      let (sel, cl, s) := keep_scan s0 hyps flags in
      if fl then (id :: sel, cl, s)
      else if in_free id s then
        (let s := Fresh.Free.union (Fresh.Free.of_constr ty) s in
         let s := match body with Some b => Fresh.Free.union (Fresh.Free.of_constr b) s | None => s end in
         (sel, cl, s))
      else (sel, id :: cl, s)
  end.
Ltac2 keep_flags_gen (onfb : unit -> unit) (k_and : constr) (hyps : (ident * constr option * constr) list) (flags : bool list) : unit :=
  let rec seeds (hyps : (ident * constr option * constr) list) (flags : bool list) (acc : constr list) : constr list :=
    match hyps with
    | [] => acc
    | h :: hyps => let (_, body, ty) := h in
                   match flags with
                   | f :: flags => seeds hyps flags (if f then decl_terms body ty acc else acc)
                   | [] => acc
                   end
    end in
  if fresh_is_plain () then
    (let s0 := free_of_list k_and (seeds hyps flags [Control.goal ()]) in
     let (sel, cl, _) := keep_scan s0 hyps flags in
     match cl with
     | [] => ()
     | _ => Control.once (fun () => Control.plus (fun () => Std.clear cl) (fun _ => onfb (); Std.keep sel))
     end)
  else Std.keep (List.fold_right (fun ((id, _, _), f) acc => if f then id :: acc else acc) (List.combine hyps flags) []).
Ltac2 keep_flags (k : ktab) (hyps : (ident * constr option * constr) list) (flags : bool list) : unit := keep_flags_gen (fun () => ()) (k.(k_and)) hyps flags.

Ltac2 prune_arith () : unit :=
  let k := mk_ktab () in
  let hyps := Control.hyps () in
  keep_flags k hyps (List.map (fun (_, _, ty) => has_arith_k k ty) hyps).

(* [comment removed for export] *)
Ltac2 atomic_flags (k : ktab) (nohard : bool) (hyps : (ident * constr option * constr) list) : bool list :=
  List.map (fun (_, _, ty) => if atomic_arith_k k ty then (if nohard then (if has_hard ty then false else true) else true) else false) hyps.
Ltac2 prune_atomic () : unit :=
  let k := mk_ktab () in
  let hyps := Control.hyps () in
  keep_flags k hyps (atomic_flags k true hyps).
Ltac prune_atomic := ltac2:(prune_atomic ()).

Ltac prune_arith := ltac2:(prune_arith ()).
(* [comment removed for export] *)
Ltac zchecker_k :=
  let __wit := fresh "__wit" in
  let __varmap := fresh "__varmap" in
  let __ff := fresh "__ff" in
  intros __wit __varmap __ff ;
  exact_no_check (Stdlib.micromega.ZMicromega.ZTautoChecker_sound __ff __wit
                    (@eq_refl bool true)
                    (@Stdlib.micromega.VarMap.find BinNums.Z BinNums.Z0 __varmap)).
(* [comment removed for export] *)
Ltac plia_cert_lazy := constr:(false).
Ltac zchecker_sel := lazymatch plia_cert_lazy with true => zchecker_k | _ => Stdlib.micromega.Lia.zchecker end.

(* [comment removed for export] *)
Ltac zify_ne := intros; zify_elim_let; zify_op; (zify_iter_specs); zify_saturate.
Ltac lia_ne := zify_ne; xlia zchecker_sel.
(* [comment removed for export] *)
Ltac lia_st := Zify.zify; xlia zchecker_sel.
(* [comment removed for export] *)
Ltac plia_full_fallback := constr:(true).
Ltac plia_last := lazymatch plia_full_fallback with false => fail | _ => lia_st end.
Ltac plia := first [ solve [ prune_atomic; lia_ne ] | solve [ prune_arith; lia_ne ] | solve [ prune_arith; lia_st ] | plia_last ].
(* [comment removed for export] *)
Ltac plia_dbg := first [ solve [ prune_atomic; lia_ne ] | idtac "PLIA-FALLBACK0"; solve [ prune_arith; lia_ne ]
                       | idtac "PLIA-FALLBACK1"; solve [ prune_arith; lia_st ]
                       | idtac "PLIA-FALLBACK2"; tryif assert_succeeds lia_st then (idtac "PLIA-T3-OK"; lia_st) else fail ].
(* [comment removed for export] *)
Ltac pnia := first [ solve [ prune_arith; Zify.zify; xnia zchecker_sel ] | Zify.zify; xnia zchecker_sel ].
(* [comment removed for export] *)
Ltac plia_v := first [ solve [ prune_atomic; zify_ne; xlia Stdlib.micromega.Lia.zchecker ] | solve [ prune_arith; zify_ne; xlia Stdlib.micromega.Lia.zchecker ] | solve [ prune_arith; Stdlib.micromega.Lia.lia ] | Stdlib.micromega.Lia.lia ].
Ltac plia_k := first [ solve [ prune_atomic; zify_ne; xlia zchecker_k ] | solve [ prune_arith; zify_ne; xlia zchecker_k ] | solve [ prune_arith; Zify.zify; xlia zchecker_k ] | Zify.zify; xlia zchecker_k ].

(* [comment removed for export] *)
Ltac2 clear_sel (k_and : constr) (sel : constr -> bool) : unit :=
  let hyps := Control.hyps () in
  let (cands, rest) := List.fold_right (fun (id, body, ty) (c, r) => if sel ty then ((id, body, ty) :: c, r) else (c, decl_terms body ty r)) hyps ([], [Control.goal ()]) in
  match cands with
  | [] => ()
  | _ =>
      if fresh_is_plain () then () else Control.zero (Tactic_failure None);
      (* [comment removed for export] *)
      let rec settle (cands : (ident * constr option * constr) list) (s : Fresh.Free.t) : ident list :=
        let (blocked, ok) := List.partition (fun (id, _, _) => in_free id s) cands in
        match blocked with
        | [] => List.map (fun (id, _, _) => id) ok
        | _ => settle ok (Fresh.Free.union s (free_of_list k_and (List.fold_right (fun (_, body, ty) acc => decl_terms body ty acc) blocked [])))
        end in
      match settle cands (free_of_list k_and rest) with [] => () | cl => Std.clear cl end
  end.
Ltac2 is_app2 (h : constr) (t : constr) : bool :=
  match Constr.Unsafe.kind (uncast t) with
  | Constr.Unsafe.App f args => if Int.equal (Array.length args) 2 then Constr.equal (uncast f) h else false
  | _ => false
  end.
Ltac2 clear_impl (all_prods : bool) : unit :=
  let k_False := Env.instantiate reference:(False) in
  let k_iff := Env.instantiate reference:(iff) in
  clear_sel (Env.instantiate reference:(and)) (fun ty =>
    match Constr.Unsafe.kind (uncast ty) with
    | Constr.Unsafe.Prod _ body =>
        if Constr.equal (uncast body) k_False then false
        else if all_prods then true else Constr.Unsafe.noccurn 1 body
    | _ => is_app2 k_iff ty
    end).
Ltac2 clear_disj () : unit := let k_or := Env.instantiate reference:(or) in clear_sel (Env.instantiate reference:(and)) (is_app2 k_or).
Ltac2 clear_zmod () : unit :=
  let k_eq := Env.instantiate reference:(eq) in
  let k_mod := Env.instantiate reference:(Z.modulo) in
  clear_sel (Env.instantiate reference:(and)) (fun ty =>
    match Constr.Unsafe.kind (uncast ty) with
    | Constr.Unsafe.App f args =>
        if Int.equal (Array.length args) 3 then (if Constr.equal (uncast f) k_eq then is_app2 k_mod (Array.get args 1) else false) else false
    | _ => false
    end).
Ltac clear_impl3 := ltac2:(Control.enter (fun () => clear_impl true)).
Ltac clear_impl2 := ltac2:(Control.enter (fun () => clear_impl false)).
Ltac clear_disj := ltac2:(Control.enter clear_disj).
Ltac clear_zmod := ltac2:(Control.enter clear_zmod).

Goal forall (x y : Z) (P : Z -> Prop) (f : Z -> Z), P x -> (forall z, P z -> z < 3)%Z -> (0 <= x)%Z -> (x < y)%Z \/ P y -> f x = 3%Z -> (x <= y)%Z -> (x < f x + y + 1)%Z.
Proof. intros. prune_arith. Fail match goal with H : P x |- _ => idtac end. plia. Qed.
Section Smoke.
  Import Stdlib.Lists.List. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Goal forall (x y : Z) (n : nat) (l : list Z), (0 <= x < 16)%Z -> (y = 2 * x + 1)%Z -> (n <= length l)%nat -> In x l -> (y <= 31 /\ 0 <= Z.of_nat n)%Z.
  Proof. intros. plia_k. Qed.
  Goal forall (x y : Z) (n : nat) (l : list Z), (0 <= x < 16)%Z -> (y = 2 * x + 1)%Z -> (n <= length l)%nat -> In x l -> (y <= 31 /\ 0 <= Z.of_nat n)%Z.
  Proof. intros. plia_v. Qed.
  Goal forall (x : Z) (P : Prop), (P /\ (x < 3)%Z) -> (P -> x < 3)%Z -> (x < 4)%Z.
  Proof. intros. plia_dbg. Qed.
  Goal forall x y : Z, (0 <= x)%Z -> (0 <= y)%Z -> (0 <= x * y)%Z.
  Proof. intros. pnia. Qed.
End Smoke.
Goal forall (x y : Z) (P Q : Prop) (f : Z -> Z), (P -> Q) -> (P -> False) -> (forall z : Z, f z = z) -> (P <-> Q) -> (x < y \/ P)%Z -> (x mod 4 = 1)%Z -> ~ Q -> (x <= y)%Z -> (x <= y)%Z.
Proof. intros x y P Q f H1 H2 H3 H4 H5 H6 H7 H8. clear_impl2. Fail clear H1. clear H3. clear_disj. Fail clear H5. clear_zmod. Fail clear H6. clear H2 H7. exact H8. Qed.
Goal forall (x y : Z) (P Q : Prop) (f : Z -> Z), (P -> Q) -> (P -> False) -> (forall z : Z, f z = z) -> (P <-> Q) -> (x <= y)%Z -> (x <= y)%Z.
Proof. intros x y P Q f H1 H2 H3 H4 H8. clear_impl3. Fail clear H3. Fail clear H4. Fail clear f. clear H2. exact H8. Qed.

End L5FastLia.
From Stdlib Require Lists.List. From Ltac2 Require Constr Control List Std.
Module L5FastTauto.
(* [comment removed for export] *)
From Stdlib Require Lists.List.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Constr Control List Std.
Set Default Proof Mode "Classic".

Ltac2 rec eq_disj (t : constr) : bool :=
  lazy_match! t with
  | ?a \/ ?b => if eq_disj a then eq_disj b else false
  | @eq _ _ _ => true
  | False => true
  | True => true
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 rec goal_leaves (t : constr) (acc : constr list) : constr list :=
  lazy_match! t with
  | ?a \/ ?b => goal_leaves a (goal_leaves b acc)
  | ?a /\ ?b => goal_leaves a (goal_leaves b acc)
  | ?a <-> ?b => goal_leaves a (goal_leaves b acc)
  | ~ ?a => goal_leaves a acc
  | ?a -> ?b => goal_leaves a (goal_leaves b acc)
  | _ => t :: acc
  end.
Ltac2 prune_eqdisj () : unit :=
  let leaves := goal_leaves (Control.goal ()) [] in
  let keepit (ty : constr) : bool := if eq_disj ty then true else List.exist (fun l => Constr.equal l ty) leaves in
  let hs := List.fold_right (fun (id, _, ty) acc => if keepit ty then id :: acc else acc) (Control.hyps ()) [] in
  Std.keep hs.
Ltac prune_eqdisj := ltac2:(prune_eqdisj ()).
(* [comment removed for export] *)
Ltac pin_disj := solve [ repeat first [ left; reflexivity | right ]; reflexivity ].
Ltac ptauto0 := first [ pin_disj | solve [ prune_eqdisj; tauto ] ].
Ltac ptauto := first [ ptauto0 | tauto ].
Ltac ptauto_dbg := first [ ptauto0 | idtac "PTAUTO-FALLBACK"; tauto ].

Goal forall (j : nat) (P Q : Prop), P /\ Q -> (P -> Q \/ P) -> 3 = j \/ 4 = j \/ False -> 4 = j \/ 7 = j \/ 3 = j \/ False.
Proof. intros j P Q H1 H2 Hj. ptauto0. Qed.
Goal forall (b : nat) (l1 l2 : list nat) (P : Prop), P /\ P -> Stdlib.Lists.List.In b l2 -> Stdlib.Lists.List.In b l1 \/ Stdlib.Lists.List.In b l2.
Proof. intros b l1 l2 P H Hb. ptauto0. Qed.
Goal exists x : nat, 3 = 4 \/ 5 = x \/ 6 = x \/ False.
Proof. eexists. ptauto0. Qed.
Goal forall (P Q : Prop), P /\ Q -> Q.
Proof. intros P Q H. Fail ptauto0. ptauto. Qed.

End L5FastTauto.
