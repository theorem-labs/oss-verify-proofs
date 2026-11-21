(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith Lia.
From Ltac2 Require Import Ltac2 Bool Constr FSet FMap Printf.

Global Unset Lia Cache.
Global Unset Nia Cache.
Set Default Proof Mode "Classic".

Import FSet.Tags.

Ltac2 Type hclass := [ HRel | HEq | HAndC | HOrC | HIffC | HNotC | HFalse | HOther ].

Ltac2 Type known := {
  rel_c : constant FSet.t;
  rel_i : inductive FSet.t;
  ty_i : inductive FSet.t;
  defer_c : constant FSet.t;
  c_iff : constant; c_not : constant;
  i_eq : inductive; i_and : inductive; i_or : inductive; i_false : inductive;
  s_prop : constr }.

Ltac2 const_of (c : constr) : constant :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constant k _ => k
  | _ => Control.throw (Invalid_argument None)
  end.
Ltac2 ind_of (c : constr) : inductive :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Ind i _ => i
  | _ => Control.throw (Invalid_argument None)
  end.

Ltac2 cset (l : constr list) : constant FSet.t :=
  List.fold_left (fun s c => FSet.add (const_of c) s) (FSet.empty constant_tag) l.
Ltac2 iset (l : constr list) : inductive FSet.t :=
  List.fold_left (fun s c => FSet.add (ind_of c) s) (FSet.empty inductive_tag) l.

Ltac2 defer_names () : ident list list :=
  [ [@zget]; [@zget_l]; [@alookup]; [@zrd]; [@zrd_l];
    [@Z; @modulo]; [@Z; @div]; [@Z; @rem]; [@Z; @quot] ].

Ltac2 resolve_consts (names : ident list list) : constant FSet.t :=
  List.fold_left (fun s n =>
      List.fold_left (fun s r =>
          match r with
          | Std.ConstRef c => FSet.add c s
          | _ => s
          end) s (Env.expand n))
    (FSet.empty constant_tag) names.

Ltac2 mk_known () : known := {
  rel_c := cset ['@Z.le; '@Z.lt; '@Z.ge; '@Z.gt; '@lt; '@ge; '@gt;
                 '@N.le; '@N.lt; '@N.ge; '@N.gt; '@Pos.le; '@Pos.lt];
  rel_i := iset ['@le];
  ty_i := iset ['Z; 'nat; 'N; 'positive; 'bool];
  defer_c := resolve_consts (defer_names ());
  c_iff := const_of '@iff; c_not := const_of '@not;
  i_eq := ind_of '@eq; i_and := ind_of '@and; i_or := ind_of '@or; i_false := ind_of 'False;
  s_prop := 'Prop }.

Ltac2 head_class (k : known) (h : constr) : hclass :=
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant c _ =>
      if FSet.mem c (k.(rel_c)) then HRel
      else if Constant.equal c (k.(c_not)) then HNotC
      else if Constant.equal c (k.(c_iff)) then HIffC
      else HOther
  | Constr.Unsafe.Ind i _ =>
      if Ind.equal i (k.(i_eq)) then HEq
      else if Ind.equal i (k.(i_and)) then HAndC
      else if Ind.equal i (k.(i_or)) then HOrC
      else if FSet.mem i (k.(rel_i)) then HRel
      else if Ind.equal i (k.(i_false)) then HFalse
      else HOther
  | _ => HOther
  end.

Ltac2 rec is_arith_carrier (k : known) (ty : constr) : bool :=
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.Ind i _ => FSet.mem i (k.(ty_i))
  | Constr.Unsafe.Constant _ _ =>
      let ty' := Std.eval_hnf ty in
      if Constr.equal ty ty' then false else is_arith_carrier k ty'
  | _ => false
  end.

Ltac2 rec is_arith (k : known) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match head_class k h with
      | HRel => true
      | HEq => is_arith_carrier k (Array.get args 0)
      | HAndC => Bool.or (is_arith k (Array.get args 0)) (is_arith k (Array.get args 1))
      | HOrC => Bool.and (is_arith k (Array.get args 0)) (is_arith k (Array.get args 1))
      | HIffC => Bool.and (is_arith k (Array.get args 0)) (is_arith k (Array.get args 1))
      | HNotC => is_arith k (Array.get args 0)
      | HFalse => false
      | HOther => false
      end
  | Constr.Unsafe.Prod b body =>
      match Constr.Binder.name b with
      | Some _ => false
      | None => Bool.and (is_arith k (Constr.Binder.type b)) (is_arith k body)
      end
  | Constr.Unsafe.Cast c _ _ => is_arith k c
  | Constr.Unsafe.Ind _ _ => match head_class k t with HFalse => true | _ => false end
  | _ => false
  end.

Ltac2 is_deferred_term (k : known) (e : constr) : bool :=
  let h := match Constr.Unsafe.kind e with
           | Constr.Unsafe.App h _ => h
           | _ => e
           end in
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant c _ => FSet.mem c (k.(defer_c))
  | Constr.Unsafe.Case _ _ _ _ _ => true
  | _ => false
  end.

Ltac2 Type aclass := [ ADrop | AKeep | ADisj | ADefer ].

Ltac2 rec head_of (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h _ => head_of h
  | Constr.Unsafe.Prod _ b => head_of b
  | Constr.Unsafe.Cast c _ _ => head_of c
  | Constr.Unsafe.LetIn _ _ b => head_of b
  | _ => t
  end.

Ltac2 rec ends_in_prop (k : known) (ty : constr) : bool :=
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.Prod _ b => ends_in_prop k b
  | Constr.Unsafe.Cast c _ _ => ends_in_prop k c
  | Constr.Unsafe.LetIn _ _ b => ends_in_prop k b
  | Constr.Unsafe.Sort _ => Constr.equal ty (k.(s_prop))
  | _ => false
  end.

Ltac2 type_ends_in_prop (k : known) (h : constr) : bool :=
  match Control.case (fun () => Constr.type h) with
  | Val p => let (ty, _) := p in ends_in_prop k ty
  | Err _ => false
  end.

Ltac2 clear_safe (ids : ident list) : unit :=
  match ids with
  | [] => ()
  | _ :: _ =>
    match Control.case (fun () => Std.clear ids) with
    | Val _ => ()
    | Err _ => List.iter (fun h => match Control.case (fun () => Std.clear [h]) with
                                   | Val _ => () | Err _ => () end) (List.rev ids)
    end
  end.

Ltac2 Type hkind := [ AVar | AProp (aclass) ].

Ltac2 prop_memo_const (k : known) (m : (constant, bool) FMap.t Ref.ref) (c : constant) (h : constr) : bool :=
  match FMap.find_opt c (Ref.get m) with
  | Some b => b
  | None => let b := type_ends_in_prop k h in Ref.set m (FMap.add c b (Ref.get m)); b
  end.

Ltac2 head_is_prop (k : known) (m : (constant, bool) FMap.t Ref.ref) (h : constr) : bool :=
  match Constr.Unsafe.kind h with
  | Constr.Unsafe.Constant c _ => prop_memo_const k m c h
  | Constr.Unsafe.Ind _ _ =>
      match head_class k h with
      | HOther => type_ends_in_prop k h
      | _ => true
      end
  | Constr.Unsafe.Sort _ => false
  | Constr.Unsafe.Rel _ => false
  | _ => type_ends_in_prop k h
  end.

Ltac2 classify_hyp (k : known) (m : (constant, bool) FMap.t Ref.ref) (t : constr) : hkind :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match head_class k h with
      | HRel => AProp AKeep
      | HEq =>
          if is_arith_carrier k (Array.get args 0) then
            if Bool.or (is_deferred_term k (Array.get args 1)) (is_deferred_term k (Array.get args 2))
            then AProp ADefer else AProp AKeep
          else AProp ADrop
      | HOrC =>
          if Bool.and (is_arith k (Array.get args 0)) (is_arith k (Array.get args 1))
          then AProp ADisj else AProp ADrop
      | HAndC =>
          if Bool.or (is_arith k (Array.get args 0)) (is_arith k (Array.get args 1))
          then AProp AKeep else AProp ADrop
      | HIffC =>
          if Bool.and (is_arith k (Array.get args 0)) (is_arith k (Array.get args 1))
          then AProp AKeep else AProp ADrop
      | HNotC => if is_arith k (Array.get args 0) then AProp AKeep else AProp ADrop
      | HFalse => AProp AKeep
      | HOther =>
          if head_is_prop k m (head_of h) then AProp ADrop else AVar
      end
  | Constr.Unsafe.Prod b body =>
      match Constr.Binder.name b with
      | None =>
          if Bool.and (is_arith k (Constr.Binder.type b)) (is_arith k body) then AProp AKeep
          else if head_is_prop k m (head_of body) then AProp ADrop else AVar
      | Some _ => if head_is_prop k m (head_of body) then AProp ADrop else AVar
      end
  | Constr.Unsafe.Ind _ _ =>
      match head_class k t with
      | HFalse => AProp AKeep
      | HOther => AVar
      | _ => AProp ADrop
      end
  | Constr.Unsafe.Constant c _ =>
      if prop_memo_const k m c t then AProp ADrop else AVar
  | Constr.Unsafe.Sort _ => AVar
  | Constr.Unsafe.Cast c _ _ => if head_is_prop k m (head_of c) then (if is_arith k c then AProp AKeep else AProp ADrop) else AVar
  | _ => if head_is_prop k m (head_of t) then (if is_arith k t then AProp AKeep else AProp ADrop) else AVar
  end.

Ltac2 Type classes := { c_drop : ident list; c_disj : ident list; c_defer : ident list;
                        c_keep : (ident * constr) list }.

Ltac2 classify (k : known) : classes :=
  let m := Ref.ref (FMap.empty constant_tag) in
  List.fold_right (fun (p : ident * constr option * constr) (acc : classes) =>
      let (h, body, t) := p in
      match body with
      | Some _ => acc
      | None =>
        match classify_hyp k m t with
        | AVar => acc
        | AProp c =>
          match c with
          | AKeep => let l := (h, t) :: acc.(c_keep) in { acc with c_keep := l }
          | ADrop => let l := h :: acc.(c_drop) in { acc with c_drop := l }
          | ADisj => let l := h :: acc.(c_disj) in { acc with c_disj := l }
          | ADefer => let l := h :: acc.(c_defer) in { acc with c_defer := l }
          end
        end
      end) (Control.hyps ()) { c_drop := []; c_disj := []; c_defer := []; c_keep := [] }.

Ltac2 rec vars_acc (k : known) (acc : ident FSet.t) (t : constr) : ident FSet.t :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var id => FSet.add id acc
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constructor _ _ => acc
      | _ => Array.fold_left (vars_acc k) (vars_acc k acc h) args
      end
  | Constr.Unsafe.Prod b body => vars_acc k (vars_acc k acc (Constr.Binder.type b)) body
  | Constr.Unsafe.Cast c _ _ => vars_acc k acc c
  | _ => acc
  end.
Ltac2 vars_of (k : known) (t : constr) : ident FSet.t := vars_acc k (FSet.empty ident_tag) t.

Ltac2 rec unconnected (s : ident FSet.t) (rest : (ident * ident FSet.t) list) : ident list :=
  let (conn, others) := List.partition (fun (p : ident * ident FSet.t) =>
                           let (_, vs) := p in Bool.neg (FSet.is_empty (FSet.inter vs s))) rest in
  match conn with
  | [] => List.map (fun (p : ident * ident FSet.t) => let (h, _) := p in h) others
  | _ :: _ =>
    let s' := List.fold_left (fun s (p : ident * ident FSet.t) => let (_, vs) := p in FSet.union s vs) s conn in
    unconnected s' others
  end.

Ltac2 ctx_sig () : constr list :=
  Control.goal () :: List.map (fun (p : ident * constr option * constr) => let (_, _, t) := p in t) (Control.hyps ()).
Ltac2 rec same_sig (a : constr list) (b : constr list) : bool :=
  match a with
  | [] => match b with [] => true | _ :: _ => false end
  | x :: a' => match b with
               | [] => false
               | y :: b' => if Constr.equal x y then same_sig a' b' else false
               end
  end.
Ltac2 lia_once (t : unit -> unit) : bool :=
  match Control.case t with
  | Val _ => true
  | Err _ => false
  end.
Ltac2 lia_nowit () : unit :=
  Control.zero (Tactic_failure (Some (Message.of_string "lia_std: cannot find witness"))).
Ltac2 lia_sat_stage () : unit :=
  let n0 := List.length (Control.hyps ()) in
  ltac1:(Zify.zify_saturate);
  let n1 := List.length (Control.hyps ()) in
  if Int.equal n0 n1 then lia_nowit ()
  else ltac1:(Zify.zify_post_hook; xlia zchecker).
Ltac2 lia_std2 () : unit :=
  Control.enter (fun () =>
    ltac1:(intros);
    if lia_once (fun () => ltac1:(xlia zchecker)) then ()
    else
      let s0 := ctx_sig () in
      ltac1:(Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; Zify.zify_iter_specs);
      let s1 := ctx_sig () in
      if same_sig s0 s1 then lia_sat_stage ()
      else if lia_once (fun () => ltac1:(Zify.zify_post_hook; xlia zchecker)) then ()
      else lia_sat_stage ()).
Ltac lia_std_fast :=
  idtac;
  lazymatch Zify.zify_convert_to_euclidean_division_equations_flag with
  | false => ltac2:(lia_std2 ())
  | _ => Zify.zify; xlia zchecker
  end.
Ltac lia_std_stock := Zify.zify; xlia zchecker.
Ltac lia_std := lia_std_fast.
Ltac2 lia1 () : unit := ltac1:(lia_std).

Ltac2 try_tier (cl : ident list) : bool :=
  match Control.case (fun () => clear_safe cl; lia1 ()) with
  | Val _ => true
  | Err _ => false
  end.

Ltac2 mutable zlia_debug () : bool := false.

Ltac2 zlia_fail () : unit :=
  Control.zero (Tactic_failure (Some (Message.of_string "zlia: lia failed on the pruned context"))).

Ltac2 zlia_tiers (k : known) (c : classes) (rel : bool) (dbg : string -> unit) : unit :=
  let drop := c.(c_drop) in
  let disj := c.(c_disj) in
  let defer := c.(c_defer) in
  let l3 := drop in
  let l2 := List.append defer l3 in
  let l1 := List.append disj l2 in
  let t0 :=
    if rel then
      let gv := vars_of k (Control.goal ()) in
      let hv := List.map (fun (p : ident * constr) => let (h, t) := p in (h, vars_of k t)) (c.(c_keep)) in
      let irrelevant := unconnected gv hv in
      match irrelevant with
      | [] => false
      | _ :: _ => try_tier (List.append irrelevant l1)
      end
    else false in
  if t0 then dbg "T0"
  else
  let single := match disj with [_] => true | _ => false end in
  if (if single then false else try_tier l1) then dbg "T1"
  else
    let t2 := match disj with [] => false | _ :: _ => try_tier l2 end in
    if t2 then dbg "T2"
    else
      match defer with
      | [] => dbg "F"; zlia_fail ()
      | _ :: _ =>
          clear_safe l3;
          match Control.case lia1 with
          | Val _ => dbg "T3"
          | Err _ => dbg "F"; zlia_fail ()
          end
      end.

Ltac2 zlia_gen (rel : bool) : unit :=
  Control.enter (fun () =>
    let k := mk_known () in
    let c := classify k in
    let dbg := if zlia_debug () then
                 let g := Control.goal () in
                 fun (tier : string) => printf "ZLDBG %s drop=%i disj=%i defer=%i keep=%i G= %t" tier
                                          (List.length (c.(c_drop))) (List.length (c.(c_disj)))
                                          (List.length (c.(c_defer))) (List.length (c.(c_keep))) g
               else fun _ => () in
    zlia_tiers k c rel dbg).

Ltac2 zlia_core2 () : unit := zlia_gen false.

Ltac2 zlia_t1_2 () : unit :=
  Control.enter (fun () =>
    let k := mk_known () in
    let c := classify k in
    clear_safe (List.append (c.(c_disj)) (List.append (c.(c_defer)) (c.(c_drop))));
    lia1 ()).
Ltac2 zlia_rel2 () : unit := zlia_gen true.

Ltac2 prune_nonarith () : unit :=
  Control.enter (fun () =>
    let k := mk_known () in
    let c := classify k in
    clear_safe (c.(c_drop))).

Ltac zprune := idtac; ltac2:(prune_nonarith ()).
Ltac zlia_core := idtac; ltac2:(zlia_core2 ()).
Ltac zlia_t1 := idtac; ltac2:(zlia_t1_2 ()).
Ltac zlia_rel := idtac; ltac2:(zlia_rel2 ()).

Ltac2 is_section_hyp (h : ident) : bool :=
  match Env.get [h] with
  | Some r => match r with Std.VarRef _ => true | _ => false end
  | None => false
  end.
Ltac2 keep_section () : unit :=
  Control.enter (fun () =>
    let sec := List.filter (fun (p : ident * constr option * constr) => let (h, _, _) := p in is_section_hyp h) (Control.hyps ()) in
    Std.keep (List.map (fun (p : ident * constr option * constr) => let (h, _, _) := p in h) sec)).
Ltac zkeep_section := idtac; ltac2:(keep_section ()).

Ltac zclear_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac zkeep_disj K :=
  repeat match goal with
         | H : _ \/ _ |- _ => tryif constr_eq H K then fail else clear H
         end.
Ltac zclear_moddiv :=
  repeat match goal with
         | H : context [Z.modulo _ _] |- _ => clear H
         | H : context [Z.div _ _] |- _ => clear H
         end.
