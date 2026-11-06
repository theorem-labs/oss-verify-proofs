(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Zify PreOmega.
From Ltac2 Require Ltac2 FSet FMap.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import LiaTuning.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import FLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require TrivLia.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RL.
  Import Ltac2.
  (* [comment removed for export] *)
  Ltac2 add_ref (r : Std.reference) (s : constant FSet.t) : constant FSet.t :=
    match r with Std.ConstRef c => FSet.add c s | _ => s end.
  Ltac2 op_consts () : constant FSet.t :=
    List.fold_left (fun s r => add_ref r s) (FSet.empty FSet.Tags.constant_tag)
    [reference:(Z.le); reference:(Z.lt); reference:(Z.add); reference:(Z.sub); reference:(Z.mul); reference:(Z.of_nat);
     reference:(not); reference:(Z.opp); reference:(Z.div); reference:(Z.modulo); reference:(Z.ge); reference:(Z.gt);
     reference:(lt); reference:(Z.to_nat)].
  Ltac2 cmp_consts () : constant FSet.t :=
    List.fold_left (fun s r => add_ref r s) (FSet.empty FSet.Tags.constant_tag)
    [reference:(Z.le); reference:(Z.lt); reference:(Z.ge); reference:(Z.gt); reference:(lt); reference:(ge); reference:(gt);
     reference:(N.le); reference:(N.lt); reference:(Z.divide)].
  Ltac2 is_ind (i : inductive) (r : Std.reference) : bool := match r with Std.IndRef i' => Ind.equal i i' | _ => false end.
  (* [comment removed for export] *)
  Ltac2 rec plain (cmp : constant FSet.t) (t : constr) : bool :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App h args =>
        match Constr.Unsafe.kind h with
        | Constr.Unsafe.Constant c _ => FSet.mem c cmp
        | Constr.Unsafe.Ind i _ =>
            if is_ind i reference:(and) then (if plain cmp (Array.get args 0) then plain cmp (Array.get args 1) else false)
            else if is_ind i reference:(eq) then true else is_ind i reference:(le)
        | _ => false
        end
    | Constr.Unsafe.Ind i _ => if is_ind i reference:(True) then true else is_ind i reference:(False)
    | _ => false
    end.
  Ltac2 is_op (ops : constant FSet.t) (h : constr) : bool :=
    match Constr.Unsafe.kind h with
    | Constr.Unsafe.Constant c _ => FSet.mem c ops
    | Constr.Unsafe.Ind i _ => if is_ind i reference:(eq) then true else if is_ind i reference:(and) then true
                               else if is_ind i reference:(or) then true else is_ind i reference:(le)
    | Constr.Unsafe.Constructor _ _ => true
    | _ => false
    end.
  Ltac2 is_poslit (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App _ args =>
        (match Constr.Unsafe.kind (Array.get args 0) with
         | Constr.Unsafe.Constructor _ _ => true
         | Constr.Unsafe.App h _ => (match Constr.Unsafe.kind h with Constr.Unsafe.Constructor _ _ => true | _ => false end)
         | _ => false
         end)
    | Constr.Unsafe.Constructor _ _ => true
    | _ => false
    end.
  Ltac2 rec mem_c (c : constr) (l : constr list) : bool :=
    match l with [] => false | x :: r => if Constr.equal c x then true else mem_c c r end.
  Ltac2 rec atoms (o : constant FSet.t) (acc : constr list) (c : constr) : constr list :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App h args =>
        if is_op o h then
          (match Constr.Unsafe.kind h with
           | Constr.Unsafe.Constructor _ _ => if is_poslit c then acc else Array.fold_left (atoms o) acc args
           | _ => Array.fold_left (atoms o) acc args
           end)
        else (if mem_c c acc then acc else c :: acc)
    | Constr.Unsafe.Constructor _ _ => acc
    | Constr.Unsafe.Ind _ _ => acc
    | Constr.Unsafe.Sort _ => acc
    | Constr.Unsafe.Cast c' _ _ => atoms o acc c'
    | _ => if mem_c c acc then acc else c :: acc
    end.
  Ltac2 rec shows (o : constant FSet.t) (g : constr list) (c : constr) : bool :=
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App h args =>
        if is_op o h then
          (match Constr.Unsafe.kind h with
           | Constr.Unsafe.Constructor _ _ => if is_poslit c then false else Array.exist (shows o g) args
           | _ => Array.exist (shows o g) args
           end)
        else mem_c c g
    | Constr.Unsafe.Constructor _ _ => false
    | Constr.Unsafe.Ind _ _ => false
    | Constr.Unsafe.Sort _ => false
    | Constr.Unsafe.Cast c' _ _ => shows o g c'
    | _ => mem_c c g
    end.
  Ltac2 rec meets (l : constr list) (g : constr list) : bool :=
    match l with [] => false | x :: r => if mem_c x g then true else meets r g end.
  Ltac2 rec union (l : constr list) (g : constr list) : constr list :=
    match l with [] => g | x :: r => if mem_c x g then union r g else union r (x :: g) end.
  Ltac2 rec round (cands : (ident * constr list) list) (g : constr list) (grown : bool) (rest : (ident * constr list) list)
    : constr list * bool * (ident * constr list) list :=
    match cands with
    | [] => (g, grown, rest)
    | x :: r => let (_, a) := x in
                if meets a g then round r (union a g) true rest else round r g grown (x :: rest)
    end.
  Ltac2 rec close (n : int) (cands : (ident * constr list) list) (g : constr list) : (ident * constr list) list :=
    if Int.le n 0 then cands else
    let (g', grown, rest) := round cands g false [] in
    let rest := List.rev rest in
    if grown then close (Int.sub n 1) rest g' else rest.
  (* [comment removed for export] *)
  Ltac2 is_prop_memo (ty : constr) (mc : (constant, bool) FMap.t) : bool * (constant, bool) FMap.t :=
    let h := LiaTuning.zt_head (LiaTuning.zt_codomain ty) in
    match Constr.Unsafe.kind h with
    | Constr.Unsafe.Constant c _ =>
        (match FMap.find_opt c mc with
         | Some b => (b, mc)
         | None => let b := LiaTuning.zt_sort_is_prop (Constr.type h) in (b, FMap.add c b mc)
         end)
    | _ => (LiaTuning.zt_is_prop ty, mc)
    end.
  Ltac2 rec classify (o : constant FSet.t) (cmp : constant FSet.t) (hs : (ident * constr option * constr) list)
      (acc : (ident * (constr list) option) list) (g : constr list) (mc : (constant, bool) FMap.t)
    : (ident * (constr list) option) list * constr list :=
    match hs with
    | [] => (List.rev acc, g)
    | h :: r =>
        let (id, body, ty) := h in
        match body with
        | Some b => classify o cmp r acc (atoms o (atoms o g (Control.hyp id)) b) mc
        | None =>
            if plain cmp ty then
              (if LiaTuning.zt_is_local id then classify o cmp r ((id, Some (atoms o [] ty)) :: acc) g mc
               else classify o cmp r acc (if shows o g ty then atoms o g ty else g) mc)
            else if LiaTuning.zt_is_local id then
              (let (b, mc') := is_prop_memo ty mc in
               if b then classify o cmp r ((id, None) :: acc) g mc' else classify o cmp r acc g mc')
            else classify o cmp r acc g mc
        end
    end.
  Ltac2 rec to_clear (all : (ident * (constr list) option) list) (drop : (ident * constr list) list) (acc : ident list) : ident list :=
    match all with
    | [] => List.rev acc
    | x :: r =>
        let (id, a) := x in
        match a with
        | None => to_clear r drop (id :: acc)
        | Some _ =>
            match drop with
            | [] => to_clear r drop acc
            | d :: dr => let (id', _) := d in
                         if Ident.equal id id' then to_clear r dr (id :: acc) else to_clear r drop acc
            end
        end
    end.
  (* [comment removed for export] *)
  Ltac2 slim_max () : int := 30.
  Ltac2 rel_prune () : unit :=
    let hs := Control.hyps () in
    if Int.le (List.length hs) (slim_max ()) then LiaTuning.zt_prune () else
    let o := op_consts () in
    let (all, g) := classify o (cmp_consts ()) hs [] (atoms o [] (Control.goal ())) (FMap.empty FSet.Tags.constant_tag) in
    let cands := List.map_filter (fun x => let (id, a) := x in match a with Some l => Some (id, l) | None => None end) all in
    let drop := close 3 cands g in
    match to_clear all drop [] with [] => () | ids => Std.clear ids end.
End RL.
Ltac rel_prune := ltac2:(Control.enter RL.rel_prune).

(* [comment removed for export] *)
Ltac lia_r12 :=
  rel_prune; intros; Zify.zify_pre_hook; zify_elim_let; zify_op; (Zify.zify_iter_specs); Zify.zify_saturate;
  first [ Zify.zify_post_hook; Z.euclidean_division_equations_cleanup; xlia zchecker
        | progress (Z.divide_to_equations'; first [ progress (repeat zify_dm_step; repeat zify_qr_step); cbv beta | idtac ]);
          Z.euclidean_division_equations_cleanup; Zify.zify_post_hook; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lia_rf3 := first [ TrivLia.lia_triv | lia_r12 | Zify.zify; xlia zchecker ].

(* [comment removed for export] *)
Ltac tlia_r := first [ rel_prune; Zify.zify; xlia zchecker
                     | Zify.zify; xlia zchecker
                     | StoreFast.sf_unhide;
                       first [ StoreFast.zify_prune_neg; Zify.zify; xlia zchecker
                             | StoreFast.zify_prune_plain; Zify.zify; xlia zchecker
                             | lia ] ].
