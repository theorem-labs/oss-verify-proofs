(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia List.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaTuning.
#[global] Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 n8k_is_const (r : Std.reference) (h : constr) : bool :=
  match Constr.Unsafe.kind h with Constr.Unsafe.Constant c _ => (match r with Std.ConstRef k => Constant.equal c k | _ => false end) | _ => false end.
Ltac2 n8k_is_ind (r : Std.reference) (h : constr) : bool :=
  match Constr.Unsafe.kind h with Constr.Unsafe.Ind i _ => (match r with Std.IndRef k => Ind.equal i k | _ => false end) | _ => false end.
Ltac2 n8k_is_ctor (r : Std.reference) (h : constr) : bool :=
  match Constr.Unsafe.kind h with Constr.Unsafe.Constructor c _ => (match r with Std.ConstructRef k => Constructor.equal c k | _ => false end) | _ => false end.
Ltac2 rec n8v_vars_d (d : int) (acc : ident list) (t : constr) : ident list :=
  if Int.le d 0 then acc else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var id => if List.mem Ident.equal id acc then acc else id :: acc
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constructor _ _ =>
          if n8k_is_ctor reference:(xO) f then acc else if n8k_is_ctor reference:(xI) f then acc else Array.fold_left (n8v_vars_d (Int.sub d 1)) acc args
      | _ => Array.fold_left (n8v_vars_d (Int.sub d 1)) (n8v_vars_d (Int.sub d 1) acc f) args
      end
  | Constr.Unsafe.Prod b c => n8v_vars_d (Int.sub d 1) (n8v_vars_d (Int.sub d 1) acc (Constr.Binder.type b)) c
  | Constr.Unsafe.Lambda b c => n8v_vars_d (Int.sub d 1) (n8v_vars_d (Int.sub d 1) acc (Constr.Binder.type b)) c
  | Constr.Unsafe.LetIn b v c => n8v_vars_d (Int.sub d 1) (n8v_vars_d (Int.sub d 1) (n8v_vars_d (Int.sub d 1) acc (Constr.Binder.type b)) v) c
  | Constr.Unsafe.Cast c _ _ => n8v_vars_d (Int.sub d 1) acc c
  | _ => acc
  end.
Ltac2 n8v_vars (acc : ident list) (t : constr) : ident list := n8v_vars_d 300 acc t.

(* [comment removed for export] *)
Ltac2 n8v_num_ty (ty : constr) : bool :=
  if n8k_is_ind reference:(Z) ty then true else if n8k_is_ind reference:(nat) ty then true else if n8k_is_ind reference:(N) ty then true else n8k_is_ind reference:(positive) ty.
Ltac2 n8v_atom (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant _ _ =>
          if n8k_is_const reference:(Z.le) h then true else if n8k_is_const reference:(Z.lt) h then true
          else if n8k_is_const reference:(Z.ge) h then true else if n8k_is_const reference:(Z.gt) h then true
          else if n8k_is_const reference:(lt) h then true else if n8k_is_const reference:(ge) h then true
          else if n8k_is_const reference:(gt) h then true else if n8k_is_const reference:(N.le) h then true
          else if n8k_is_const reference:(N.lt) h then true else n8k_is_const reference:(Z.divide) h
      | Constr.Unsafe.Ind _ _ =>
          if n8k_is_ind reference:(eq) h then n8v_num_ty (Array.get args 0) else n8k_is_ind reference:(le) h
      | _ => false
      end
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 rec n8v_scan (acc : bool * ident list) (t : constr) : bool * ident list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if n8v_atom t then (let (_, vs) := acc in (true, n8v_vars vs t))
      else if Int.equal (Array.length args) 2 then
        (if n8k_is_ind reference:(and) h then n8v_scan (n8v_scan acc (Array.get args 0)) (Array.get args 1)
         else if n8k_is_ind reference:(or) h then n8v_scan (n8v_scan acc (Array.get args 0)) (Array.get args 1)
         else if n8k_is_const reference:(iff) h then n8v_scan (n8v_scan acc (Array.get args 0)) (Array.get args 1)
         else acc)
      else if Int.equal (Array.length args) 1 then (if n8k_is_const reference:(not) h then n8v_scan acc (Array.get args 0) else acc)
      else acc
  | Constr.Unsafe.Prod b c =>
      if Constr.Unsafe.closedn 0 c then n8v_scan (n8v_scan acc (Constr.Binder.type b)) c else acc
  | _ => acc
  end.

(* [comment removed for export] *)
Ltac2 rec n8v_plain (t : constr) : bool :=
  if n8v_atom t then true else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Int.equal (Array.length args) 2 then
        (if n8k_is_ind reference:(and) h then (if n8v_plain (Array.get args 0) then n8v_plain (Array.get args 1) else false) else false)
      else false
  | Constr.Unsafe.Prod b c =>
      if Constr.Unsafe.closedn 0 c then
        (if n8v_plain c then (let (has, vs) := n8v_scan (false, []) (Constr.Binder.type b) in
                              if has then (match vs with [] => true | _ :: _ => false end) else false) else false)
      else false
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 n8v_is_placed (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h _ =>
      match Constr.Unsafe.kind h with
      | Constr.Unsafe.Constant c _ =>
          (match List.rev (Env.path (Std.ConstRef c)) with
           | id :: _ => Ident.equal id @placed
           | [] => false end)
      | _ => false
      end
  | _ => false
  end.

Ltac2 n8v_shares (vs : ident list) (ws : ident list) : bool := List.exist (fun v => List.mem Ident.equal v ws) vs.
Ltac2 n8v_union (acc : ident list) (vs : ident list) : ident list :=
  List.fold_left (fun a v => if List.mem Ident.equal v a then a else v :: a) acc vs.

(* [comment removed for export] *)
Ltac2 rec n8v_loop (k : int) (hp : int) (hn : int) (bud : int) (vars : ident list) (sel : ident list)
                   (rest : (ident * int * ident list) list) (conn : (ident list) list) : ident list :=
  if Int.gt k hp then sel else
  let np_ok := Int.le k hn in
  let (hit, miss) := List.partition (fun p => let (_, cl, vs) := p in
                        if (if Int.equal cl 0 then true else np_ok) then n8v_shares vs vars else false) rest in
  (* [comment removed for export] *)
  let (hit, back, bud') :=
    List.fold_left (fun acc p => let (h, bk, bd) := acc in let (_, cl, _) := p in
                      if Int.equal cl 1 then (if Int.gt bd 0 then (p :: h, bk, Int.sub bd 1) else (h, p :: bk, bd)) else (p :: h, bk, bd))
                   ([], [], bud) hit in
  let (chit, cmiss) := List.partition (fun vs => n8v_shares vs vars) conn in
  match hit with
  | [] => (match chit with
           | [] => sel
           | _ :: _ => n8v_loop k hp hn bud' (List.fold_left n8v_union vars chit) sel (List.append back miss) cmiss end)
  | _ :: _ =>
      let vars' := List.fold_left (fun acc p => let (_, _, vs) := p in n8v_union acc vs) (List.fold_left n8v_union vars chit) hit in
      n8v_loop (Int.add k 1) hp hn bud' vars' (List.append sel (List.map (fun p => let (id, _, _) := p in id) hit)) (List.append back miss) cmiss
  end.

Ltac2 n8v_clear_each (ids : ident list) : unit :=
  List.iter (fun id => Control.once (fun () => Control.plus (fun () => Std.clear [id]) (fun _ => ()))) ids.
Ltac2 n8v_clear (ids : ident list) : unit :=
  match ids with
  | [] => ()
  | _ :: _ => Control.once (fun () => Control.plus (fun () => Std.clear ids) (fun _ => n8v_clear_each (List.rev ids)))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 n8v_numeric_ty (ty : constr) : bool :=
  let h := match Constr.Unsafe.kind ty with Constr.Unsafe.App f _ => f | _ => ty end in
  if n8k_is_ind reference:(Z) h then true else if n8k_is_ind reference:(nat) h then true else if n8k_is_ind reference:(N) h then true
  else if n8k_is_ind reference:(positive) h then true else if n8k_is_ind reference:(list) h then true
  else match Constr.Unsafe.kind h with
       | Constr.Unsafe.Constant c _ =>
           (match List.rev (Env.path (Std.ConstRef c)) with
            | id :: _ => if Ident.equal id @bv then true else Ident.equal id @word
            | [] => false end)
       | Constr.Unsafe.Ind i _ =>
           (match List.rev (Env.path (Std.IndRef i)) with
            | id :: _ => Ident.equal id @bv
            | [] => false end)
       | _ => false
       end.
Ltac2 rec n8v_take (n : int) (l : 'a list) : 'a list :=
  if Int.le n 0 then [] else match l with [] => [] | x :: r => x :: n8v_take (Int.sub n 1) r end.
Ltac2 n8v_minus (vs : ident list) (hubs : ident list) : ident list :=
  match hubs with [] => vs | _ :: _ => List.filter (fun v => Bool.neg (List.mem Ident.equal v hubs)) vs end.

(* [comment removed for export] *)
Ltac2 n8v_prune (hp : int) (hn : int) (bud : int) (keep_placed : bool) (seed : int) : unit :=
  let hs := Control.hyps () in
  (* [comment removed for export] *)
  let pc := { contents := FMap.empty FSet.Tags.constant_tag } in
  let ic := { contents := [] } in
  let is_prop_c (ty : constr) : bool :=
    let h := LiaTuning.zt_head (LiaTuning.zt_codomain ty) in
    match Constr.Unsafe.kind h with
    | Constr.Unsafe.Constant c _ =>
        (match FMap.find_opt c (pc.(contents)) with
         | Some b => b
         | None => let b := LiaTuning.zt_is_prop ty in pc.(contents) := FMap.add c b (pc.(contents)); b
         end)
    | Constr.Unsafe.Ind i _ =>
        (match List.find_opt (fun p => let (j, _) := p in Ind.equal i j) (ic.(contents)) with
         | Some p => let (_, b) := p in b
         | None => let b := LiaTuning.zt_is_prop ty in ic.(contents) := (i, b) :: ic.(contents); b
         end)
    | _ => LiaTuning.zt_is_prop ty
    end in
  (* [comment removed for export] *)
  let (cands, junk, conn, placed, hubs) :=
    List.fold_left (fun acc h =>
      let (cands, junk, conn, placed, hubs) := acc in
      let (id, body, ty) := h in
      match body with
      | Some b => (cands, junk, (id :: n8v_vars [] b) :: conn, placed, hubs)
      | None =>
          if n8v_is_placed ty then (cands, junk, conn, (id, 2, n8v_vars [] ty) :: placed, hubs) else
          let (has, vs) := n8v_scan (false, []) ty in
          if has then ((id, (if n8v_plain ty then 0 else 1), vs) :: cands, junk, conn, placed, hubs)
          else if LiaTuning.zt_is_local id then (if is_prop_c ty then (cands, id :: junk, conn, placed, hubs) else acc)
          else if n8v_numeric_ty ty then acc
          else (cands, junk, conn, placed, id :: hubs)
      end) ([], [], [], [], []) hs in
  (* [comment removed for export] *)
  let strip := fun p => let (id, cl, vs) := p in if Int.equal cl 0 then p else (id, cl, n8v_minus vs hubs) in
  let cands := List.map strip cands in
  let placed := List.map strip placed in
  (* [comment removed for export] *)
  let gvars := n8v_vars [] (Control.goal ()) in
  let gvars := if Int.le seed 0 then gvars else
    List.fold_left (fun acc p => let (_, _, vs) := p in n8v_union acc vs) gvars
      (n8v_take seed (List.filter (fun p => let (id, _, _) := p in LiaTuning.zt_is_local id) cands)) in
  let gvars := if Int.lt hp 0 then [] else gvars in
  let ids := fun l => List.map (fun p => let (id, _, _) := p in id) l in
  match gvars with
  | [] => n8v_clear (List.append junk (ids placed))
  | _ :: _ =>
      (* [comment removed for export] *)
      let pure := fun l => List.map_filter (fun p => let (id, cl, vs) := p in
                                    if Int.equal cl 0 then None else match vs with [] => Some id | _ :: _ => None end) l in
      let small := Int.le (List.length cands) 14 in
      let sel := if small then ids (List.append cands placed) else
                 List.append (n8v_loop 1 hp hn bud gvars [] (List.append cands (if keep_placed then placed else [])) conn)
                             (List.append (pure cands) (if keep_placed then pure placed else [])) in
      let irrel := List.filter (fun id => Bool.neg (List.mem Ident.equal id sel)) (ids cands) in
      let pdrop := if keep_placed then List.filter (fun id => Bool.neg (List.mem Ident.equal id sel)) (ids placed) else ids placed in
      let (irrel_local, irrel_sec) := List.partition LiaTuning.zt_is_local irrel in
      n8v_clear (List.append junk (List.append pdrop irrel_local));
      n8v_clear irrel_sec
  end.

Ltac n8v_prune1p := ltac2:(Control.enter (fun () => n8v_prune 1 0 0 false 0)).        (* [comment removed for export] *)
Ltac n8v_prune1 := ltac2:(Control.enter (fun () => n8v_prune 1 1 8 false 0)).         (* [comment removed for export] *)
Ltac n8v_prunep := ltac2:(Control.enter (fun () => n8v_prune 1000 3 8 false 0)).      (* [comment removed for export] *)
Ltac n8v_prune_all := ltac2:(Control.enter (fun () => n8v_prune (-1) 0 0 false 0)).
Ltac n8v_prunec := ltac2:(Control.enter (fun () => n8v_prune 1000 1000 1000 false 0)).
Ltac n8v_prune_placed := ltac2:(Control.enter (fun () => n8v_prune 2 2 8 true 0)).
Ltac n8v_prune_seed := ltac2:(Control.enter (fun () => n8v_prune 1000 2 8 false 12)).

(* [comment removed for export] *)
Ltac2 n8v_show_recent (k : int) : unit :=
  let hs := List.rev (Control.hyps ()) in
  let rec go (n : int) (l : (ident * constr option * constr) list) : unit :=
    if Int.le n 0 then () else
    match l with
    | [] => ()
    | h :: r => let (id, _, ty) := h in
        Message.print (Message.concat (Message.of_string "   RECENT ") (Message.concat (Message.of_ident id) (Message.concat (Message.of_string " : ") (Message.of_constr ty))));
        go (Int.sub n 1) r
    end in go k hs.
Ltac n8v_show_recent := ltac2:(Control.enter (fun () => n8v_show_recent 5)).

(* [comment removed for export] *)
Goal forall a b c d e x : Z, (a < b)%Z -> (b < x)%Z -> (x < c)%Z -> (d < e)%Z -> (e < 0 \/ 0 < e)%Z -> (a < c)%Z.
Proof. intros a b c d e x H1 H2 H3 H4 H5. n8v_prunep. lia. Qed.
Goal forall a b : Z, (a < b)%Z -> (b < a)%Z -> False.
Proof. intros a b H1 H2. n8v_prunec. lia. Qed.
Goal forall a b x : Z, let l := (a + 1)%Z in (l < b)%Z -> (b < x)%Z -> (a < x)%Z.
Proof. intros a b x l H1 H2. n8v_prunec. lia. Qed.
