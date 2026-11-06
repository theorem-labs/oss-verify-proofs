(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Import Ltac2.
#[global] Set Default Proof Mode "Classic".
From stdpp.bitvector Require Import definitions.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaTuning Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition pin_mark {T : Type} (x : T) : unit := tt.
Definition pin_ceil_mark {T : Type} (x : T) : unit := tt.
(* [comment removed for export] *)
Ltac pin_using x :=
  let P := fresh "PIN__" in pose (P := pin_mark x);
  try (match goal with c : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.CEIL |- ?G =>
         lazymatch G with context [c] => let Q := fresh "PINCEIL__" in pose (Q := pin_ceil_mark c) end end).

Ltac2 rec lp_binder_names (t : constr) : ident list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Lambda b body =>
      (match Constr.Binder.name b with
       | Some n => n :: lp_binder_names body
       | None => lp_binder_names body
       end)
  | Constr.Unsafe.Cast c _ _ => lp_binder_names c
  | _ => []
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 rec lp_strip_cast (t : constr) : constr :=
  match Constr.Unsafe.kind t with Constr.Unsafe.Cast c _ _ => lp_strip_cast c | _ => t end.
Ltac2 lp_pin_head (b : constr) : bool :=
  match Constr.Unsafe.kind (lp_strip_cast b) with
  | Constr.Unsafe.App f _ => (let f' := lp_strip_cast f in
                              match Constr.Unsafe.kind f' with
                              | Constr.Unsafe.Constant _ _ => lt_is_ref f' reference:(pin_mark)
                              | _ => true
                              end)
  | _ => false
  end.
Ltac2 lp_pin_names () : (ident list) option :=
  List.fold_left (fun acc h => let (_, body, _) := h in
      match acc with
      | Some _ => acc
      | None => match body with
                | Some b => if lp_pin_head b then (match! b with pin_mark ?f => Some (lp_binder_names f) | _ => None end) else None
                | None => None
                end
      end) None (Control.hyps ()).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 lp_clear_each (ids : ident list) : unit :=
  List.iter (fun id => Control.once (fun () => Control.plus (fun () => Std.clear [id]) (fun _ => ()))) ids.
Ltac2 lp_clear_unpinned () : unit :=
  match lp_pin_names () with
  | None => ()
  | Some names =>
      let mm := zt_memo_new () in   (* [comment removed for export] *)
      let todo := List.map_filter (fun h => let (id, body, ty) := h in
        match body with
        | Some _ => None
        | None =>
            if zt_is_local id then None
            else if zt_is_prop_m mm ty then (if List.exist (Ident.equal id) names then None else Some id)
            else None
        end) (Control.hyps ()) in
      match todo with
      | [] => ()
      | [_] => lp_clear_each todo
      | _ :: _ :: _ =>
          let n := List.length todo in
          if List.for_all (fun id => Constr.Unsafe.noccur_between 1 n (Constr.Unsafe.closenl todo 1 (Constr.type (Control.hyp id)))) todo
          then Control.once (fun () => Control.plus (fun () => Std.clear todo) (fun _ => lp_clear_each todo))
          else lp_clear_each todo
      end
  end.
(* [comment removed for export] *)
Ltac clear_unpinned := once ltac2:(Control.enter lp_clear_unpinned).

(* [comment removed for export] *)
Ltac clear_or_hyps := once (repeat match goal with H : ?T |- _ => lazymatch T with context [or] => clear H end end).

Ltac lia_base3 := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                        | zify_prune; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Inductive liafast_marker : Prop := LiaFastMode.
Ltac lia_fast_mode_on := lazymatch goal with | _ : liafast_marker |- _ => idtac | _ => fail end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 rec lp_arith_prop (t : constr) : bool :=
  if zt_plain_arith t then true else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if lt_is_ref h reference:(or) then (if lp_arith_prop (Array.get args 0) then lp_arith_prop (Array.get args 1) else false)
      else if lt_is_ref h reference:(and) then (if lp_arith_prop (Array.get args 0) then lp_arith_prop (Array.get args 1) else false)
      else if lt_is_ref h reference:(not) then lp_arith_prop (Array.get args 0)
      else if lt_is_ref h reference:(iff) then (if lp_arith_prop (Array.get args 0) then lp_arith_prop (Array.get args 1) else false)
      else false
  | Constr.Unsafe.Prod b body =>
      if lp_arith_prop (Constr.Binder.type b) then (if Constr.Unsafe.closedn 0 body then lp_arith_prop body else false) else false
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 rec lp_keep (t : constr) : bool :=
  if zt_plain_arith t then true else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if lt_is_ref h reference:(or) then (if lp_keep (Array.get args 0) then true else lp_keep (Array.get args 1))
      else if lt_is_ref h reference:(and) then (if lp_keep (Array.get args 0) then true else lp_keep (Array.get args 1))
      else if lt_is_ref h reference:(not) then lp_keep (Array.get args 0)
      else if lt_is_ref h reference:(iff) then (if lp_keep (Array.get args 0) then true else lp_keep (Array.get args 1))
      else false
  | Constr.Unsafe.Prod b body =>
      if Constr.Unsafe.closedn 0 body then (if lp_keep (Constr.Binder.type b) then true else lp_keep body) else false
  | _ => false
  end.
Ltac2 lp_is_and0 (t : constr) : bool :=
  match Constr.Unsafe.kind t with Constr.Unsafe.App h _ => lt_is_ref h reference:(and) | _ => false end.
(* [comment removed for export] *)
Ltac2 rec lp_mentions_or (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if lt_is_ref h reference:(or) then true
      else if (if lt_is_ref h reference:(not) then lp_is_and0 (Array.get args 0) else false) then true
      else Array.exist lp_mentions_or args
  | Constr.Unsafe.Prod b body => if lp_mentions_or (Constr.Binder.type b) then true else lp_mentions_or body
  | _ => false
  end.
Ltac2 lp_is_or (t : constr) : bool :=
  match Constr.Unsafe.kind t with Constr.Unsafe.App h _ => lt_is_ref h reference:(or) | _ => false end.
Ltac2 lp_is_and (t : constr) : bool :=
  match Constr.Unsafe.kind t with Constr.Unsafe.App h _ => lt_is_ref h reference:(and) | _ => false end.
Ltac2 rec lp_vars (acc : ident list) (t : constr) : ident list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var i => if List.exist (Ident.equal i) acc then acc else i :: acc
  | Constr.Unsafe.App f args => Array.fold_left lp_vars (lp_vars acc f) args
  | Constr.Unsafe.Cast c _ _ => lp_vars acc c
  | Constr.Unsafe.Prod b body => lp_vars (lp_vars acc (Constr.Binder.type b)) body
  | Constr.Unsafe.Lambda b body => lp_vars (lp_vars acc (Constr.Binder.type b)) body
  | Constr.Unsafe.LetIn b v body => lp_vars (lp_vars (lp_vars acc (Constr.Binder.type b)) v) body
  | _ => acc
  end.
Ltac2 rec lp_shares (vars : ident list) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var i => List.exist (Ident.equal i) vars
  | Constr.Unsafe.App f args => if lp_shares vars f then true else Array.exist (lp_shares vars) args
  | Constr.Unsafe.Cast c _ _ => lp_shares vars c
  | Constr.Unsafe.Prod b body => if lp_shares vars (Constr.Binder.type b) then true else lp_shares vars body
  | _ => false
  end.
Ltac2 lp_clear_ids (ids : ident list) : unit :=
  match ids with
  | [] => ()
  | _ :: _ =>
      (* [comment removed for export] *)
      Control.once (fun () => Control.plus (fun () => Std.clear ids)
        (fun _ => List.iter (fun id => Control.once (fun () => Control.plus (fun () => Std.clear [id]) (fun _ => ()))) ids))
  end.
(* [comment removed for export] *)
Ltac2 lp_prune_K () : unit :=
  lp_clear_ids (List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None => if zt_is_prop ty then (if lp_keep ty then None else Some id) else None   (* [comment removed for export] *)
      end) (Control.hyps ())).
Ltac2 lp_clear_or_walk () : unit :=
  lp_clear_ids (List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None => if lp_mentions_or ty then (if zt_is_prop ty then Some id else None) else None
      end) (Control.hyps ())).
(* [comment removed for export] *)
Ltac2 lp_or_add (r : ident list Ref.ref) (h : ident) : unit :=
  if List.exist (Ident.equal h) (Ref.get r) then () else Ref.set r (h :: Ref.get r).
Ltac2 lp_or_superset () : ident list :=
  let r := Ref.ref [] in
  let _ := Control.case (fun () => multi_match! goal with [ h : context [ or ] |- _ ] => lp_or_add r h; Control.zero Match_failure end) in
  let _ := Control.case (fun () => multi_match! goal with [ h : context [ ~ (_ /\ _) ] |- _ ] => lp_or_add r h; Control.zero Match_failure end) in
  Ref.get r.
Ltac2 lp_clear_or () : unit :=
  match lp_or_superset () with
  | [] => ()
  | sup =>
    let ids := List.filter (fun id => match Control.hyp_value id with
                                     | Some _ => false
                                     | None => let ty := Constr.type (Control.hyp id) in
                                               if lp_mentions_or ty then zt_is_prop ty else false
                                     end) sup in
    match ids with
    | [] => ()
    | _ :: _ => Control.once (fun () => Control.plus (fun () => Std.clear ids) (fun _ => lp_clear_or_walk ()))
    end
  end.
(* [comment removed for export] *)
Ltac clear_or_hyps_orig := once (repeat match goal with H : ?T |- _ => lazymatch T with context [or] => clear H end end).
Ltac2 lp_or_hyps_all () : ident list :=
  let r := Ref.ref [] in
  let _ := Control.case (fun () => multi_match! goal with [ h : context [ or ] |- _ ] => lp_or_add r h; Control.zero Match_failure end) in
  Ref.get r.
Ltac2 lp_clear_or_hyps () : unit :=
  match lp_or_hyps_all () with
  | [] => ()
  | ids => Control.once (fun () => Control.plus (fun () => Std.clear ids) (fun _ => ltac1:(clear_or_hyps_orig)))
  end.
Ltac clear_or_hyps ::= ltac2:(Control.enter lp_clear_or_hyps).
(* [comment removed for export] *)
Ltac2 rec lp_has_divmod_term (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if (match Constr.Unsafe.kind h with
          | Constr.Unsafe.Constant _ _ =>
              if lt_is_ref h reference:(Z.div) then true else if lt_is_ref h reference:(Z.modulo) then true
              else if lt_is_ref h reference:(Z.quot) then true else if lt_is_ref h reference:(Z.rem) then true
              else if lt_is_ref h reference:(Nat.div) then true else if lt_is_ref h reference:(Nat.modulo) then true
              else if lt_is_ref h reference:(N.div) then true else if lt_is_ref h reference:(N.modulo) then true
              else if lt_is_ref h reference:(Z.divide) then true else false
          | _ => false
          end) then true
      else Array.exist lp_has_divmod_term args
  | Constr.Unsafe.Prod b body => if lp_has_divmod_term (Constr.Binder.type b) then true else lp_has_divmod_term body
  | Constr.Unsafe.Cast c _ _ => lp_has_divmod_term c
  | _ => false
  end.
Ltac2 lp_has_divmod_walk () : bool :=
  if lp_has_divmod_term (Control.goal ()) then true
  else List.exist (fun h => let (_, body, ty) := h in
         if lp_has_divmod_term ty then true else match body with Some b => lp_has_divmod_term b | None => false end) (Control.hyps ()).
(* [comment removed for export] *)
Ltac2 lp_dm_flags () : Std.red_flags :=
  { Std.rStrength := Std.Norm; Std.rBeta := false; Std.rMatch := false; Std.rFix := false; Std.rCofix := false;
    Std.rZeta := false; Std.rDelta := false;
    Std.rConst := [reference:(Z.div); reference:(Z.modulo); reference:(Z.quot); reference:(Z.rem); reference:(Nat.div);
                   reference:(Nat.modulo); reference:(N.div); reference:(N.modulo); reference:(Z.divide)] }.
Ltac2 lp_no_divmod_in (parts : constr list) : bool :=
  match parts with
  | [] => true
  | _ :: _ =>
      let all := Constr.Unsafe.make (Constr.Unsafe.App 'True (Array.of_list parts)) in
      Constr.equal all (Std.eval_cbv (lp_dm_flags ()) all)
  end.
Ltac2 lp_has_divmod () : bool :=
  (* [comment removed for export] *)
  if (if lp_no_divmod_in [Control.goal ()] then false else lp_has_divmod_term (Control.goal ())) then true
  else
    let hs := Control.hyps () in
    let parts := List.fold_left (fun acc h => let (_, body, ty) := h in
                   match body with Some b => b :: ty :: acc | None => ty :: acc end) [] hs in
    if lp_no_divmod_in parts then false
    else List.exist (fun h => let (_, body, ty) := h in
           if lp_has_divmod_term ty then true else match body with Some b => lp_has_divmod_term b | None => false end) hs.
Ltac lp_divmod_present := ltac2:(Control.enter (fun () => if lp_has_divmod () then () else Control.zero (Tactic_failure None))).
Ltac lp_solver_K := first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | lp_divmod_present; Zify.zify; xlia zchecker ].
Ltac lp_node_solver := ltac2:(Control.enter lp_clear_or); lp_solver_K.

Ltac2 lp_candidates () : (ident * constr) list :=
  List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None => if lp_is_or ty then (if lp_arith_prop ty then Some (id, ty) else None) else None
      end) (Control.hyps ()).
(* [comment removed for export] *)
Ltac2 lp_is_w2g (id : ident) : bool :=
  let s := Ident.to_string id in
  if Int.lt (String.length s) 3 then false
  else if Char.equal (String.get s 0) (String.get "W2G" 0) then
         (if Char.equal (String.get s 1) (String.get "W2G" 1) then Char.equal (String.get s 2) (String.get "W2G" 2) else false)
       else false.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 rec lp_shvars (acc : ident list) (t : constr) : ident list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var i => if List.exist (Ident.equal i) acc then acc else i :: acc
  | Constr.Unsafe.App f args => Array.fold_left lp_shvars (lp_shvars acc f) args
  | Constr.Unsafe.Cast c _ _ => lp_shvars acc c
  | Constr.Unsafe.Prod b body => lp_shvars (lp_shvars acc (Constr.Binder.type b)) body
  | _ => acc
  end.
Ltac2 lp_count_shared (vars : ident list) (t : constr) : int :=
  let sv := lp_shvars [] t in
  List.fold_left (fun n v => if List.exist (Ident.equal v) sv then Int.add n 1 else n) 0 vars.
Ltac2 lp_ranked_candidates () : (ident * int) list :=
  let cands := List.rev (lp_candidates ()) in
  let gv := List.fold_left (fun acc h => let (id, _, ty) := h in if lp_is_w2g id then lp_vars acc ty else acc)
              (lp_vars [] (Control.goal ())) (Control.hyps ()) in
  let scored := List.map (fun p => let (id, ty) := p in (id, lp_count_shared gv ty)) cands in
  let ge2 := List.filter (fun p => let (_, k) := p in Int.ge k 2) scored in
  let eq1 := List.filter (fun p => let (_, k) := p in Int.equal k 1) scored in
  let eq0 := List.filter (fun p => let (_, k) := p in Int.equal k 0) scored in
  List.append ge2 (List.append eq1 eq0).
Ltac2 lp_ordered_candidates () : ident list := List.map (fun p => let (id, _) := p in id) (lp_ranked_candidates ()).
Ltac2 lp_split_and_hyps () : bool :=
  List.fold_left (fun acc h => let (id, body, ty) := h in
      match body with
      | Some _ => acc
      | None => if lp_is_and ty then (if lp_mentions_or ty then (if lp_arith_prop ty then
                   (ltac1:(h |- let a := fresh "W2A" in let b := fresh "W2A" in destruct h as [a b]) (Ltac1.of_ident id);
                    lp_clear_ids [id]; true) else acc) else acc) else acc
      end) false (Control.hyps ()).
Ltac2 lp_try (tac : unit -> unit) : bool :=
  match Control.case (fun () => Control.once tac) with
  | Val _ => true
  | Err _ => false
  end.
(* [comment removed for export] *)
Ltac2 lp_split (id : ident) : unit :=
  ltac1:(h |- let a := fresh "W2D" in let b := fresh "W2D" in destruct h as [a|b]) (Ltac1.of_ident id);
  Control.enter (fun () => lp_clear_ids [id]).

Ltac2 Type exn ::= [ LpBudget | LpProbe (bool) | LpNotUseful ].
(* [comment removed for export] *)
Ltac2 rec lp_probe (fuel : int) : unit :=
  match lp_ordered_candidates () with
  | [] => if lp_try (fun () => ltac1:(lp_solver_K)) then Control.zero (LpProbe true) else Control.zero (LpProbe false)
  | id :: _ =>
      if Int.le fuel 0 then Control.zero (LpProbe true) else
      (lp_split id;
       let left_closed := Control.focus 1 1 (fun () => lp_try (fun () => ltac1:(lp_node_solver))) in
       if left_closed then
         (* [comment removed for export] *)
         (if lp_try (fun () => ltac1:(lp_node_solver)) then Control.zero (LpProbe true) else Control.enter (fun () => lp_probe (Int.sub fuel 1)))
       else Control.focus 1 1 (fun () => lp_probe (Int.sub fuel 1)))
  end.
(* [comment removed for export] *)
Ltac2 lp_tiered () : unit :=
  let ranked := lp_ranked_candidates () in
  let n := List.length ranked in
  let drop (minshare : int) : ident list := List.map_filter (fun p => let (id, k) := p in if Int.lt k minshare then Some id else None) ranked in
  let d2 := drop 2 in let d1 := drop 1 in
  let attempt (ids : ident list) : bool := lp_try (fun () => lp_clear_ids ids; ltac1:(lp_solver_K)) in
  if (if Int.lt (List.length d2) n then (if Int.gt (List.length d2) 0 then attempt d2 else false) else false) then ()
  else if (if Int.lt (List.length d1) (List.length d2) then (if Int.gt (List.length d1) 0 then attempt d1 else false) else false) then ()
  else ltac1:(lp_solver_K).
(* [comment removed for export] *)
Ltac2 rec lp_careful (work : int Ref.ref) : unit :=
  Control.enter (fun () =>
    Ref.incr work;
    if Int.gt (Ref.get work) 48 then Control.zero LpBudget else
    if lp_try (fun () => ltac1:(lp_node_solver)) then () else
    match lp_ordered_candidates () with
    | [] => ltac1:(lp_solver_K)
    | ids =>
        let rec try_useful (l : ident list) (k : int) : bool :=
          match l with
          | [] => false
          | id :: rest =>
              if Int.le k 0 then false else
              (Ref.set work (Int.add (Ref.get work) 2);
               if Int.gt (Ref.get work) 48 then Control.zero LpBudget else
               let ok := lp_try (fun () =>
                           lp_split id;
                           Control.enter (fun () => if lp_try (fun () => ltac1:(lp_node_solver)) then () else ());
                           if Int.ge (Control.numgoals ()) 2 then Control.zero LpNotUseful else ()) in
               if ok then true else try_useful rest (Int.sub k 1))
          end in
        if try_useful ids 8 then lp_careful work else lp_tiered ()
    end).
(* [comment removed for export] *)
Ltac2 lp_num_type (t : constr) : bool :=
  if lt_is_ref t reference:(Z) then true else if lt_is_ref t reference:(nat) then true else if lt_is_ref t reference:(N) then true else lt_is_ref t reference:(positive).
Ltac2 rec lp_strict_arith (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if lt_is_ref h reference:(eq) then lp_num_type (Array.get args 0)
      else if lt_is_ref h reference:(and) then (if lp_strict_arith (Array.get args 0) then lp_strict_arith (Array.get args 1) else false)
      else if lt_is_ref h reference:(or) then (if lp_strict_arith (Array.get args 0) then lp_strict_arith (Array.get args 1) else false)
      else if lt_is_ref h reference:(not) then lp_strict_arith (Array.get args 0)
      else if lt_is_ref h reference:(Z.le) then true else if lt_is_ref h reference:(Z.lt) then true
      else if lt_is_ref h reference:(Z.ge) then true else if lt_is_ref h reference:(Z.gt) then true
      else if lt_is_ref h reference:(le) then true else if lt_is_ref h reference:(lt) then true
      else if lt_is_ref h reference:(ge) then true else if lt_is_ref h reference:(gt) then true
      else if lt_is_ref h reference:(N.le) then true else if lt_is_ref h reference:(N.lt) then true
      else false
  | Constr.Unsafe.Ind _ _ => if lt_is_ref t reference:(True) then true else lt_is_ref t reference:(False)
  | _ => false
  end.
Ltac lp_goal_strict := ltac2:(Control.enter (fun () => if lp_strict_arith (Control.goal ()) then () else Control.zero (Tactic_failure None))).
Ltac lp_syn_close :=
  lp_goal_strict;
  match goal with
  | H : ?T |- ?G => constr_eq T G; exact H
  | G : ?P, H : ~ ?Q |- False => constr_eq P Q; exact (H G)
  end.
(* [comment removed for export] *)
Ltac2 rec lp_neg_disj (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if lt_is_ref h reference:(and) then
        (let a := lp_neg_disj (Array.get args 0) in let b := lp_neg_disj (Array.get args 1) in constr:($a \/ $b))
      else constr:(~ $t)
  | _ => constr:(~ $t)
  end.
Ltac2 lp_convert_negs () : unit :=
  List.iter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => ()
      | None =>
          match Constr.Unsafe.kind ty with
          | Constr.Unsafe.App hd args =>
              if (if lt_is_ref hd reference:(not) then (if lp_is_and0 (Array.get args 0) then lp_arith_prop (Array.get args 0) else false) else false) then
                (let d := lp_neg_disj (Array.get args 0) in
                 if lp_try (fun () => ltac1:(h d |- let n := fresh "W2N" in assert (n : d) by (clear - h; lp_solver_K)) (Ltac1.of_ident id) (Ltac1.of_constr d))
                 then lp_clear_ids [id] else ())
              else ()
          | _ => ()
          end
      end) (Control.hyps ()).
Ltac2 lp_intro_neg_goal () : unit :=
  match Constr.Unsafe.kind (Control.goal ()) with
  | Constr.Unsafe.App hd args =>
      if (if lt_is_ref hd reference:(not) then lp_strict_arith (Array.get args 0) else false) then ltac1:(let g := fresh "W2G" in intro g) else ()
  | _ => ()
  end.
Ltac2 lp_dpll_root () : unit :=
  Control.enter (fun () =>
    if lp_try (fun () => ltac1:(lp_syn_close)) then () else
    (lp_intro_neg_goal ();
     if lp_try (fun () => ltac1:(lp_syn_close)) then () else
     (lp_convert_negs ();
      let n := List.length (lp_candidates ()) in
      if Int.lt n 6 then lp_tiered ()
      else
        let verdict := match Control.case (fun () => lp_probe 40) with
                       | Val _ => true
                       | Err e => match e with LpProbe b => b | _ => true end
                       end in
        if verdict then
          match Control.case (fun () => Control.once (fun () => lp_careful (Ref.ref 0))) with
          | Val _ => ()
          | Err e => match e with
                     | LpBudget => lp_tiered ()
                     | _ => Control.zero (Tactic_failure None)
                     end
          end
        else Control.zero (Tactic_failure None)))).
(* [comment removed for export] *)
Ltac2 rec lp_dpll_conj () : unit :=
  Control.enter (fun () =>
    if lp_is_and (Control.goal ()) then (ltac1:(split); lp_dpll_conj ()) else lp_dpll_root ()).
Ltac2 lp_dpll_goal () : unit :=
  Control.enter (fun () =>
    lp_prune_K ();
    (if lp_split_and_hyps () then (if lp_split_and_hyps () then (let _ := lp_split_and_hyps () in ()) else ()) else ());
    lp_dpll_conj ()).
(* [comment removed for export] *)
Ltac2 lp7_ranked () : (ident * int) list :=
  let cands := List.rev (lp_candidates ()) in
  let gv := List.fold_left (fun acc h => let (id, _, ty) := h in if lp_is_w2g id then lp_vars acc ty else acc)
              (lp_vars [] (Control.goal ())) (Control.hyps ()) in
  let scored := List.map (fun p => let (id, ty) := p in (id, lp_count_shared gv ty)) cands in
  let mx := List.fold_left (fun m p => let (_, k) := p in if Int.gt k m then k else m) 0 scored in
  let rec go k acc := if Int.lt k 0 then acc else
      go (Int.sub k 1) (List.append acc (List.filter (fun p => let (_, j) := p in Int.equal j k) scored)) in
  go mx [].
Ltac2 lp7_ordered () : ident list := List.map (fun p => let (id, _) := p in id) (lp7_ranked ()).
Ltac2 rec lp7_skipn (k : int) (l : 'a list) : 'a list := if Int.le k 0 then l else match l with [] => [] | _ :: r => lp7_skipn (Int.sub k 1) r end.
(* [comment removed for export] *)
Ltac2 lp7_leaf_provable (lft : bool) : bool :=
  let cs := lp_candidates () in
  let ids := List.map (fun p => let (id, _) := p in id) cs in
  let lit ty := match Constr.Unsafe.kind ty with Constr.Unsafe.App _ args => Array.get args (if lft then 0 else 1) | _ => ty end in
  let imp := List.fold_right (fun p acc => let (_, ty) := p in let l := lit ty in constr:($l -> $acc)) cs (Control.goal ()) in
  match Control.case (fun () =>
      ltac1:(t |- assert t) (Ltac1.of_constr imp);
      Control.focus 1 1 (fun () => lp_clear_ids ids; ltac1:(lp_solver_K));
      Control.zero (LpProbe true)) with
  | Val _ => true
  | Err e => match e with LpProbe b => b | _ => false end
  end.
Ltac2 rec lp7_probe (fuel : int) : unit :=
  match lp7_ordered () with
  | [] => if lp_try (fun () => ltac1:(lp_solver_K)) then Control.zero (LpProbe true) else Control.zero (LpProbe false)
  | id :: _ =>
      if Int.le fuel 0 then Control.zero (LpProbe true) else
      (lp_split id;
       let left_closed := Control.focus 1 1 (fun () => lp_try (fun () => ltac1:(lp_node_solver))) in
       if left_closed then
         (if lp_try (fun () => ltac1:(lp_node_solver)) then Control.zero (LpProbe true) else Control.enter (fun () => lp7_probe (Int.sub fuel 1)))
       else Control.focus 1 1 (fun () => lp7_probe (Int.sub fuel 1)))
  end.
Ltac2 rec lp7_careful (work : int Ref.ref) (tried : bool) : unit :=
  Control.enter (fun () =>
    Ref.incr work;
    if Int.gt (Ref.get work) 48 then Control.zero LpBudget else
    if (if tried then false else lp_try (fun () => ltac1:(lp_node_solver))) then () else
    match lp7_ordered () with
    | [] => ltac1:(lp_solver_K)
    | ids =>
        let rec try_useful (l : ident list) (k : int) : bool :=
          match l with
          | [] => false
          | id :: rest =>
              if Int.le k 0 then false else
              (Ref.set work (Int.add (Ref.get work) 2);
               if Int.gt (Ref.get work) 48 then Control.zero LpBudget else
               let ok := lp_try (fun () =>
                           lp_split id;
                           Control.enter (fun () => if lp_try (fun () => ltac1:(lp_node_solver)) then () else ());
                           if Int.ge (Control.numgoals ()) 2 then Control.zero LpNotUseful else ()) in
               if ok then true else try_useful rest (Int.sub k 1))
          end in
        if try_useful ids 8 then lp7_careful work true else lp_tiered ()
    end).
Ltac2 lp7_dpll_root () : unit :=
  Control.enter (fun () =>
    if lp_try (fun () => ltac1:(lp_syn_close)) then () else
    (lp_intro_neg_goal ();
     if lp_try (fun () => ltac1:(lp_syn_close)) then () else
     (lp_convert_negs ();
      let n := List.length (lp_candidates ()) in
      if Int.lt n 6 then lp_tiered ()
      else
        let keep_best (k : int) : bool :=
          let drop := List.map (fun p => let (id, _) := p in id) (lp7_skipn k (lp7_ranked ())) in
          lp_try (fun () => lp_clear_ids drop; ltac1:(lp_solver_K)) in
        if keep_best 3 then () else
        if Bool.neg (lp7_leaf_provable true) then Control.zero (Tactic_failure None) else
        if keep_best 5 then () else
        if lp7_leaf_provable false then
          (let verdict := match Control.case (fun () => lp7_probe 40) with
                          | Val _ => true
                          | Err e => match e with LpProbe b => b | _ => true end
                          end in
           if verdict then
             match Control.case (fun () => Control.once (fun () => lp7_careful (Ref.ref 0) false)) with
             | Val _ => ()
             | Err e => match e with
                        | LpBudget => lp_tiered ()
                        | _ => Control.zero (Tactic_failure None)
                        end
             end
           else Control.zero (Tactic_failure None))
        else Control.zero (Tactic_failure None)))).
Ltac2 rec lp7_dpll_conj () : unit :=
  Control.enter (fun () =>
    if lp_is_and (Control.goal ()) then (ltac1:(split); lp7_dpll_conj ()) else lp7_dpll_root ()).
Ltac2 lp7_dpll_goal () : unit :=
  Control.enter (fun () =>
    lp_prune_K ();
    (if lp_split_and_hyps () then (if lp_split_and_hyps () then (let _ := lp_split_and_hyps () in ()) else ()) else ());
    lp7_dpll_conj ()).
Ltac lia_dpll := ltac2:(lp7_dpll_goal ()).


Ltac lia_fast := zify_prune; clear_or_hyps;
  first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | lp_divmod_present; Zify.zify; xlia zchecker ].      (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 lp_head_beta () : unit :=
  match Constr.Unsafe.kind (Control.goal ()) with
  | Constr.Unsafe.App f _ => (match Constr.Unsafe.kind f with Constr.Unsafe.Lambda _ _ => ltac1:(cbv beta) | _ => () end)
  | _ => ()
  end.
Ltac head_beta := ltac2:(Control.enter lp_head_beta).
Ltac pinned_lia_core := head_beta; first [ lia_fast | tryif lia_fast_mode_on then fail else lia_dpll ].
Ltac pinned_lia := clear_unpinned; pinned_lia_core.

(* [comment removed for export] *)
Ltac2 rec lp_mentions_var (id : ident) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var i => Ident.equal i id
  | Constr.Unsafe.App f args => if lp_mentions_var id f then true else Array.exist (lp_mentions_var id) args
  | Constr.Unsafe.Cast c _ _ => lp_mentions_var id c
  | Constr.Unsafe.Prod b body => if lp_mentions_var id (Constr.Binder.type b) then true else lp_mentions_var id body
  | Constr.Unsafe.Lambda b body => if lp_mentions_var id (Constr.Binder.type b) then true else lp_mentions_var id body
  | _ => false
  end.
Ltac2 lp_ceil_ok () : unit :=
  match lp_pin_names () with
  | None => ()
  | Some names =>
      let hs := Control.hyps () in
      (* [comment removed for export] *)
      let marked := List.exist (fun h => let (_, body, _) := h in
                        match body with Some b => (match! b with pin_ceil_mark _ => true | _ => false end) | None => false end) hs in
      if marked then () else
      (* [comment removed for export] *)
      let ok := List.exist (fun h => let (id, _, ty) := h in
                   match! ty with
                   | OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.CEIL =>
                       if List.exist (Ident.equal id) names then true
                       else List.exist (fun h2 => let (id2, _, ty2) := h2 in
                                          if List.exist (Ident.equal id2) names then lp_mentions_var id ty2 else false) hs
                   | _ => false
                   end) hs in
      if ok then () else Control.zero (Tactic_failure None)
  end.
Ltac ceil_ok := ltac2:(Control.enter lp_ceil_ok).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac syn_assumption := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Ltac noevar_assumption := syn_assumption.
(* [comment removed for export] *)
Tactic Notation "fastfirst" tactic3(t) := first [ (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [t]) | t ].

(* [comment removed for export] *)
Module LiaPinSelfTest.
Section SelfTest.
  Variables a b c : Z.
  Hypothesis H1 : (a <= b)%Z.
  Hypothesis H2 : (a <= 5 \/ 7 <= a)%Z.
  Hypothesis H3 : (b <= c)%Z.
  Lemma t1 : (a <= c)%Z.
  Proof using H1 H3. pin_using (fun (H1 H3 : unit) => tt). pinned_lia. Qed.
  Lemma t2 : (a <> 6)%Z.
  Proof using H2. pin_using (fun (H2 : unit) => tt). pinned_lia. Qed.
  #[using="b H1 H3"] Lemma t3 : (a <= c)%Z.      (* [comment removed for export] *)
  Proof. pinned_lia. Qed.
  Lemma t4 : (a <= a)%Z.      (* [comment removed for export] *)
  Proof using Type. pin_using tt. pinned_lia. Qed.
  (* [comment removed for export] *)
  Hypothesis H4 : (a <= c)%Z.
  Lemma t5 : (a <= c)%Z.
  Proof using H1 H3. pin_using (fun (H1 H3 : unit) => tt). pinned_lia. Qed.
  Lemma t6 : (a <= c)%Z.
  Proof using H4. pin_using (fun (H4 : unit) => tt). pinned_lia. Qed.
  Lemma t7 : (a <= 5 \/ 7 <= a)%Z /\ (a <= c)%Z.
  Proof using H1 H2 H3. pin_using (fun (H1 H2 H3 : unit) => tt).
    split; fastfirst (first [ exact H2 | pinned_lia ]). Qed.
  Lemma t8 : (a <> 6)%Z.      (* [comment removed for export] *)
  Proof using H2. pin_using (fun (H2 : unit) => tt). fastfirst (first [ reflexivity | pinned_lia ]). Qed.
End SelfTest.
Section SelfTestCeil.
  Context {CEILV : CEIL}.
  Variable a : Z.
  Hypothesis HA : (a <= alloc_ceiling)%Z.
  Hypothesis HB : (a <= 5)%Z.
  Local Ltac tlia := clear_unpinned; try (ceil_ok; ceil_facts); pinned_lia_core.
  Lemma c1 : (a < 2^47)%Z.                (* [comment removed for export] *)
  Proof using HA. pin_using (fun (HA : unit) => tt). tlia. Qed.
  Lemma c2 : (a <= 6)%Z.                  (* [comment removed for export] *)
  Proof using HB. pin_using (fun (HB : unit) => tt). tlia. Qed.
  Lemma c3 : (0 < alloc_ceiling)%Z.       (* [comment removed for export] *)
  Proof using Type. pin_using tt. tlia. Qed.
End SelfTestCeil.
Lemma b1 (P a : Z) : (P <= a < P + 24)%Z -> (fun a0 : Z => (P <= a0 < P + 24 \/ P + 32 <= a0 < P + 648)%Z) a.
Proof. intros H. pinned_lia. Qed.
End LiaPinSelfTest.
