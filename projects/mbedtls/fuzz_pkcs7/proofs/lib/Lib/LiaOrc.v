(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Import Ltac2 Int Char String FSet FMap Fresh.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaTuning.
#[global] Set Default Proof Mode "Classic".
#[global] Unset Lia Cache.
#[global] Unset Nia Cache.
#[global] Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lia_ref :=
  first [ zify_prune;
          first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                | Zify.zify; xlia zchecker ]
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Ltac lia_t12_ref := first [ LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Lemma orc_keep : forall (A : Type), A -> True -> True.
Proof. exact (fun _ _ p => p). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 mutable tbl : unit -> string := fun () => "".
Ltac2 mutable record : unit -> bool := fun () => false.
(* [comment removed for export] *)
Ltac2 mutable tag : unit -> string := fun () => "-".
(* [comment removed for export] *)
Ltac2 mutable trace : unit -> bool := fun () => false.

Ltac2 Type hint := [ HFail | HKeep (string list) ].

(* [comment removed for export] *)
Ltac2 d64 (s : string) (p : int) : int := Int.sub (Char.to_int (String.get s p)) 48.
Ltac2 rd2 (s : string) (p : int) : int := Int.add (Int.mul (d64 s p) 64) (d64 s (Int.add p 1)).
Ltac2 rd3 (s : string) (p : int) : int := Int.add (Int.mul (rd2 s p) 64) (d64 s (Int.add p 2)).
Ltac2 rec bsearch (s : string) (key : string) (kw : int) (lo : int) (hi : int) : int :=
  if Int.lt hi lo then -1 else
  let mid := Int.asr (Int.add lo hi) 1 in
  let c := String.compare (String.sub s (Int.add 5 (Int.mul mid kw)) kw) key in
  if Int.equal c 0 then mid
  else if Int.lt c 0 then bsearch s key kw (Int.add mid 1) hi
  else bsearch s key kw lo (Int.sub mid 1).
Ltac2 rec names_at (s : string) (p : int) (e : int) (acc : string list) : string list :=
  if Int.le e p then List.rev acc
  else let l := d64 s p in names_at s (Int.add (Int.add p 1) l) e (String.sub s (Int.add p 1) l :: acc).
Ltac2 lookup_in (s : string) (d : string) : hint option :=
  let ls := String.length s in
  if Int.lt ls 5 then None else
  let n := rd3 s 0 in
  let kw := rd2 s 3 in
  let ld := String.length d in
  if Int.lt kw ld then None else
  let key := if Int.equal kw ld then d else String.app d (String.make (Int.sub kw ld) (Char.of_int 32)) in
  let i := bsearch s key kw 0 (Int.sub n 1) in
  if Int.lt i 0 then None else
  let ob := Int.add 5 (Int.mul n kw) in
  let pb := Int.add ob (Int.mul 3 (Int.add n 1)) in
  let o1 := Int.add pb (rd3 s (Int.add ob (Int.mul 3 i))) in
  let o2 := Int.add pb (rd3 s (Int.add ob (Int.mul 3 (Int.add i 1)))) in
  if Int.equal (Char.to_int (String.get s o1)) 70 (* [comment removed for export] *) then Some HFail
  else Some (HKeep (names_at s (Int.add o1 1) o2 [])).

(* [comment removed for export] *)
(* [comment removed for export] *)
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
           if Constructor.equal c (x.(c_Zpos)) then mix x (Int.add 11 (Int.mul 16 (pos_bits x (Array.get args 0) 10 1 0)))
           else if Constructor.equal c (x.(c_Zneg)) then mix x (Int.add 13 (Int.mul 16 (pos_bits x (Array.get args 0) 10 1 0)))
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
  match l with [] => (n, last) | hd :: r => match r with [] => (let (id, _, _) := hd in (Int.add n 1, Some id)) | _ :: _ => len_last r (Int.add n 1) last end end.
Ltac2 digest_of (g : constr) (hyps : (ident * constr option * constr) list) : string :=
  let x := dmk () in
  walk x 3 g;
  let (n, last) := len_last hyps 0 None in
  (match last with Some id => mix x (Int.add 97 (name_code (Ident.to_string id))) | None => () end);
  String.concat "." [dec (Int.land (x.(h)) 68719476735); dec n].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 is_section_entry (id : ident) : bool := match Env.get [id] with None => false | Some _ => true end.
(* [comment removed for export] *)
Ltac2 used_entries (p : constr) (hyps : (ident * constr option * constr) list) : ident list :=
  let s := Fresh.Free.of_constr p in
  List.map_filter (fun h => let (id, _, _) := h in if Ident.equal (Fresh.fresh s id) id then None else Some id) hyps.
Ltac2 say (l : string list) : unit := Message.print (Message.of_string (String.concat " " ("LIAREC" :: l))).
(* [comment removed for export] *)
Ltac2 term_of (tac : Ltac1.t) : constr :=
  let g := Control.goal () in
  let r := { contents := None } in
  Ltac1.apply ltac1val:(fun g tac => constr:(ltac:(tac) : g)) [Ltac1.of_constr g; tac] (fun v => r.(contents) := Ltac1.to_constr v);
  match r.(contents) with Some p => p | None => Control.zero (Tactic_failure None) end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 tr (m : string) (d : string) : unit := if trace () then Message.print (Message.of_string (String.concat " " [m; tag (); d])) else ().
(* [comment removed for export] *)
Ltac2 mem_free (s : Fresh.Free.t) (u : ident) : bool := Bool.neg (Ident.equal (Fresh.fresh s u) u).
(* [comment removed for export] *)
Ltac2 Type kenv := { k_or : inductive; k_eq : inductive; k_Z : inductive; k_bv : inductive; k_not : constant; k_mod : constant; k_lt : constant }.
Ltac2 kind_ind (c : constr) : inductive := match Constr.Unsafe.kind c with Constr.Unsafe.Ind i _ => i | _ => Control.throw Not_found end.
Ltac2 kind_const (c : constr) : constant := match Constr.Unsafe.kind c with Constr.Unsafe.Constant k _ => k | _ => Control.throw Not_found end.
Ltac2 kmk () : kenv :=
  { k_or := kind_ind '@or; k_eq := kind_ind '@eq; k_Z := kind_ind 'Z; k_bv := kind_ind '@stdpp.bitvector.definitions.bv;
    k_not := kind_const '@not; k_mod := kind_const '@Z.modulo; k_lt := kind_const '@Z.lt }.
Ltac2 is_ind (i : inductive) (c : constr) : bool :=
  match Constr.Unsafe.kind c with Constr.Unsafe.Ind j _ => Ind.equal i j | _ => false end.
Ltac2 is_const (k : constant) (c : constr) : bool :=
  match Constr.Unsafe.kind c with Constr.Unsafe.Constant j _ => Constant.equal k j | _ => false end.
(* [comment removed for export] *)
Ltac2 k_is_or (e : kenv) (ty : constr) : bool :=
  match Constr.Unsafe.kind ty with Constr.Unsafe.App h _ => is_ind (e.(k_or)) h | _ => false end.
(* [comment removed for export] *)
Ltac2 k_is_modapp (e : kenv) (t : constr) : bool :=
  match Constr.Unsafe.kind t with Constr.Unsafe.App h _ => is_const (e.(k_mod)) h | _ => false end.
(* [comment removed for export] *)
Ltac2 k_is_modfact (e : kenv) (ty : constr) : bool :=
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.App h args =>
      if is_ind (e.(k_eq)) h then
        (if Int.equal (Array.length args) 3 then
           (if k_is_modapp e (Array.get args 1) then true else k_is_modapp e (Array.get args 2))
         else false)
      else if is_const (e.(k_not)) h then
        (if Int.equal (Array.length args) 1 then
           match Constr.Unsafe.kind (Array.get args 0) with
           | Constr.Unsafe.App h2 a2 =>
               if is_ind (e.(k_eq)) h2 then (if Int.equal (Array.length a2) 3 then k_is_modapp e (Array.get a2 1) else false) else false
           | _ => false
           end
         else false)
      else if is_const (e.(k_lt)) h then
        (if Int.equal (Array.length args) 2 then k_is_modapp e (Array.get args 0) else false)
      else false
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 k_is_zbv (e : kenv) (ty : constr) : bool :=
  match Constr.Unsafe.kind ty with
  | Constr.Unsafe.Ind i _ => Ind.equal i (e.(k_Z))
  | Constr.Unsafe.App h args => if is_ind (e.(k_bv)) h then Int.equal (Array.length args) 1 else false
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 split_ctx (keep : ident FSet.t) (gfv : Fresh.Free.t) (hyps : (ident * constr option * constr) list)
  : ident list * (constr * constr) list * bool :=
  List.fold_left (fun acc h => let (dead, sec, ev) := acc in let (id, _, ty) := h in
      if Bool.or (FSet.mem id keep) (mem_free gfv id)
      then (dead, (if is_section_entry id then (Control.hyp id, ty) :: sec else sec), (if ev then true else Constr.has_evar ty))
      else (id :: dead, sec, ev)) ([], [], false) hyps.
(* [comment removed for export] *)
Ltac2 touch_term (sec : (constr * constr) list) : constr :=
  (* [comment removed for export] *)
  List.fold_right (fun p acc => let (c, _) := p in constr:(@orc_keep _ $c $acc)) sec constr:(I).
(* [comment removed for export] *)
Ltac2 closure_keep (ids : ident list) : unit :=
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
  | _ :: _ => match Control.case (fun () => Std.clear dead) with Val _ => () | Err _ => Std.keep ids end
  end.
Ltac2 solve_with (tac : Ltac1.t) : unit :=
  Ltac1.run tac; Control.enter (fun () => Control.zero (Tactic_failure None)).
(* [comment removed for export] *)
Ltac2 hit_fast (names : ident list) (hyps : (ident * constr option * constr) list) (hit : Ltac1.t) : unit :=
  let keep := List.fold_left (fun s id => FSet.add id s) (FSet.empty FSet.Tags.ident_tag) names in
  (* [comment removed for export] *)
  let hd := Env.instantiate reference:(True) in
  let parts := Control.goal () :: List.flatten (List.map (fun h => let (id, body, ty) := h in
                 if FSet.mem id keep then (match body with Some b => [b; ty] | None => [ty] end) else []) hyps) in
  let gfv := Fresh.Free.of_constr (Constr.Unsafe.make (Constr.Unsafe.App hd (Array.of_list parts))) in
  let (dead, sec, ev) := split_ctx keep gfv hyps in
  (* [comment removed for export] *)
  (if ev then Control.zero (Tactic_failure None) else ());
  (match sec with
   | [] => Std.clear dead
   | _ :: _ =>
       (* [comment removed for export] *)
       let nm := @orc_touch_ in Std.pose (Some nm) (touch_term sec); Std.clear (nm :: dead)
   end);
  solve_with hit.
(* [comment removed for export] *)
Ltac2 hit_careful (names : ident list) (hit : Ltac1.t) : unit :=
  let hyps := Control.hyps () in
  let present := List.filter (fun id => List.exist (fun h => let (j, _, _) := h in Ident.equal j id) hyps) names in
  match present with
  | [] => (match names with [] => () | _ :: _ => Control.zero (Tactic_failure None) end); closure_keep []; solve_with hit
  | _ :: _ =>
      if List.exist (fun id => Constr.has_evar (Constr.type (Control.hyp id))) present then Control.zero (Tactic_failure None) else
      (closure_keep present;
       let hyps2 := Control.hyps () in
       let sec := List.map_filter (fun h => let (id, _, ty) := h in
                    if is_section_entry id then (if List.exist (Ident.equal id) present then Some (Control.hyp id, ty) else None) else None) hyps2 in
       (match sec with [] => () | _ :: _ => let nm := Fresh.in_goal @orc_touch in Std.pose (Some nm) (touch_term sec); Std.clear [nm] end);
       solve_with hit)
  end.

(* [comment removed for export] *)
Ltac2 go (pfx : string) (tac : Ltac1.t) (hit : Ltac1.t) : unit :=
  let run_ref () := Ltac1.run tac in
  if record () then
    (let g := Control.goal () in
     if Constr.has_evar g then run_ref () else
     let hyps := Control.hyps () in
     let d := String.app pfx (digest_of g hyps) in
     match Control.case (fun () => term_of tac) with
     | Val r => let (p, _) := r in
                let ids := used_entries p hyps in
                say (tag () :: d :: "S" :: dec (List.length ids) :: List.map Ident.to_string ids);
                Std.exact_no_check p
     | Err _ => say [tag (); d; "F"]; Control.zero (Tactic_failure None)
     end)
  else
  let t := tbl () in
  if Int.equal (String.length t) 0 then run_ref () else
  let g := Control.goal () in
  let hyps := Control.hyps () in
  if Constr.has_evar g then (tr "ORCEVAR" (String.app pfx (digest_of g hyps)); run_ref ()) else
  let d := String.app pfx (digest_of g hyps) in
  match lookup_in t d with
  | None => tr "ORCMISS" d; run_ref ()
  | Some (HFail) => tr "ORCFAIL" d; Control.zero (Tactic_failure (Some (Message.of_string "lia (oracle: recorded failure)")))
  | Some (HKeep names0) =>
      let names := List.map_filter Ident.of_string names0 in
      Control.once (fun () => Control.plus
        (fun () => hit_fast names hyps hit; tr "ORCHIT" d)
        (fun _ => Control.plus
          (fun () => hit_careful names hit; tr "ORCHIT2" d)
          (fun _ => tr "ORCFALL" d; run_ref ())))
  end.

(* [comment removed for export] *)
Ltac orc_go_L tac := let f := ltac2:(tac |- Control.enter (fun () => go "L" tac tac)) in f tac.
Ltac orc_go_T tac := let f := ltac2:(tac |- Control.enter (fun () => go "T" tac tac)) in f tac.
Ltac orc_go_Q tac := let f := ltac2:(tac |- Control.enter (fun () => go "Q" tac tac)) in f tac.
Ltac orc_go_P tac := let f := ltac2:(tac |- Control.enter (fun () => go "P" tac tac)) in f tac.
Ltac orc_go_D tac := let f := ltac2:(tac |- Control.enter (fun () => go "D" tac tac)) in f tac.
Ltac orc_go_K tac := let f := ltac2:(tac |- Control.enter (fun () => go "K" tac tac)) in f tac.
Ltac orc_go_R tac := let f := ltac2:(tac |- Control.enter (fun () => go "R" tac tac)) in f tac.
Ltac orc_go_O tac := let f := ltac2:(tac |- Control.enter (fun () => go "O" tac tac)) in f tac.
Ltac orc_go_N tac := let f := ltac2:(tac |- Control.enter (fun () => go "N" tac tac)) in f tac.
Ltac orc_go_M tac := let f := ltac2:(tac |- Control.enter (fun () => go "M" tac tac)) in f tac.
Ltac orc_go_C tac := let f := ltac2:(tac |- Control.enter (fun () => go "C" tac tac)) in f tac.
Ltac orc_go_AH tac := let f := ltac2:(tac |- Control.enter (fun () => go "L" tac tac)) in f tac.
(* [comment removed for export] *)
Ltac orc_lia := orc_go_L ltac:(lia_ref).
Ltac orc_lia_t12 := orc_go_T ltac:(lia_t12_ref).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac orc_mentions_goal_var T :=
  match goal with
  | x : Z |- _ => lazymatch T with context [x] => lazymatch goal with |- context [x] => idtac end end
  | x : stdpp.bitvector.definitions.bv _ |- _ => lazymatch T with context [x] => lazymatch goal with |- context [x] => idtac end end
  end.
Ltac orc_prune_disj_ref :=
  repeat match goal with H : ?A \/ ?B |- _ => tryif orc_mentions_goal_var (A \/ B) then fail else clear H end.
Ltac orc_clear_mods_ref :=
  lazymatch goal with
  | |- context [Z.modulo _ _] => idtac
  | _ => repeat match goal with
         | H : Z.modulo _ _ = _ |- _ => clear H
         | H : _ = Z.modulo _ _ |- _ => clear H
         | H : Z.modulo _ _ <> _ |- _ => clear H
         | H : Z.modulo _ _ < _ |- _ => clear H
         end
  end.
Ltac2 rec fc_fix (ids : ident list) : unit :=
  let (progress, rest) := List.fold_left (fun acc id => let (pr, rest) := acc in
      match Control.case (fun () => Std.clear [id]) with Val _ => (true, rest) | Err _ => (pr, id :: rest) end) (false, []) ids in
  if progress then (match rest with [] => () | _ :: _ => fc_fix (List.rev rest) end) else ().
Ltac2 fc_clear_list (ids : ident list) : unit :=
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with Val _ => () | Err _ => fc_fix ids end
  end.
(* [comment removed for export] *)
Ltac2 fc_disj_ids (e : kenv) : ident list :=
  List.fold_left (fun acc h => let (id, _, ty) := h in if k_is_or e ty then id :: acc else acc) [] (Control.hyps ()).
Ltac2 fc_clear_disj () : unit := fc_clear_list (fc_disj_ids (kmk ())).

(* [comment removed for export] *)
Ltac2 rec k_mentions_const (k : constant) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Constant j _ => Constant.equal k j
  | Constr.Unsafe.App h args => if k_mentions_const k h then true else Array.exist (k_mentions_const k) args
  | Constr.Unsafe.Prod b c => if k_mentions_const k (Constr.Binder.type b) then true else k_mentions_const k c
  | Constr.Unsafe.Lambda b c => if k_mentions_const k (Constr.Binder.type b) then true else k_mentions_const k c
  | Constr.Unsafe.LetIn b v c => if k_mentions_const k (Constr.Binder.type b) then true else if k_mentions_const k v then true else k_mentions_const k c
  | Constr.Unsafe.Cast c _ _ => k_mentions_const k c
  | Constr.Unsafe.Case _ _ _ c brs => if k_mentions_const k c then true else Array.exist (k_mentions_const k) brs
  | Constr.Unsafe.Proj _ _ c => k_mentions_const k c
  | _ => false
  end.
Ltac2 fc_clear_mods () : unit :=
  let e := kmk () in
  if Constr.has_evar (Control.goal ()) then ltac1:(orc_clear_mods_ref) else
  if k_mentions_const (e.(k_mod)) (Control.goal ()) then ()
  else fc_clear_list (List.fold_left (fun acc h => let (id, _, ty) := h in if k_is_modfact e ty then id :: acc else acc) [] (Control.hyps ())).

(* [comment removed for export] *)
Ltac2 fc_prune_disj () : unit :=
  if Constr.has_evar (Control.goal ()) then ltac1:(orc_prune_disj_ref) else
  let e := kmk () in
  let hyps := Control.hyps () in
  let gfv := Fresh.Free.of_constr (Control.goal ()) in
  let vars := List.map_filter (fun h => let (id, _, ty) := h in
                if k_is_zbv e ty then (if mem_free gfv id then Some id else None) else None) hyps in
  let ids := List.fold_left (fun acc h => let (id, _, ty) := h in
               if k_is_or e ty then
                 (let fv := Fresh.Free.of_constr ty in
                  if List.exist (fun v => mem_free fv v) vars then acc else id :: acc)
               else acc) [] hyps in
  fc_clear_list ids.

(* [comment removed for export] *)
Ltac2 fc_keep_disj1 (d : constr) : unit :=
  let e := kmk () in
  let keep := match Constr.Unsafe.kind d with Constr.Unsafe.Var id => Some id | _ => None end in
  let ids := List.fold_left (fun acc h => let (id, _, ty) := h in
               if k_is_or e ty then
                 (match keep with Some k => if Ident.equal k id then acc else id :: acc | None => id :: acc end)
               else acc) [] (Control.hyps ()) in
  fc_clear_list ids.

Ltac fc_clear_disj := ltac2:(Control.enter fc_clear_disj).
Ltac fc_clear_mods := ltac2:(Control.enter fc_clear_mods).
Ltac fc_prune_disj := ltac2:(Control.enter fc_prune_disj).
Ltac fc_keep_disj1 D := let f := ltac2:(d |- Control.enter (fun () => fc_keep_disj1 (Option.get (Ltac1.to_constr d)))) in f D.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac qlia_ref := fc_clear_disj; fc_clear_mods; lia_ref.          (* [comment removed for export] *)
Ltac pqlia_ref := fc_prune_disj; fc_clear_mods; lia_ref.         (* [comment removed for export] *)
Ltac dlia_ref := fc_clear_disj; lia_ref.                         (* [comment removed for export] *)
Ltac plia_ref := fc_prune_disj; lia_ref.                         (* [comment removed for export] *)
Ltac lia1_ref D := fc_keep_disj1 D; fc_clear_mods; lia_ref.      (* [comment removed for export] *)
Ltac orc_qlia := orc_go_Q ltac:(qlia_ref).
Ltac orc_pqlia := orc_go_P ltac:(pqlia_ref).
Ltac orc_dlia := orc_go_D ltac:(dlia_ref).
Ltac orc_plia := orc_go_R ltac:(plia_ref).
Ltac orc_lia1 D := orc_go_K ltac:(lia1_ref D).
(* [comment removed for export] *)
