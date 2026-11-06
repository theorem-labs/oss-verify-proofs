(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import GwApply GwApply2 GwFold.
From Ltac2 Require Import Ltac2 Constr Control Message Bool Env.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Set Default Proof Mode "Classic".

Definition gwt_pat {A B : Type} (p : A) (d : B) (rest : unit) : unit := tt.

Definition gwt_def {A B : Type} (g : A) (d : B) (rest : unit) : unit := tt.

Definition gwt_unf {A : Type} (c : A) (rest : unit) : unit := tt.

Definition gwt_hdr {A B : Type} (h : A) (d : B) (rest : unit) : unit := tt.

Definition gwt_zc (c : Z) (rest : unit) : unit := tt.
Definition gwt_nil : unit := tt.

Ltac2 rec gwt_is_pos (t : constr) : bool :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f a => if Bool.or (Constr.equal f 'xI) (Constr.equal f 'xO) then gwt_is_pos (Array.get a 0) else false
| _ => Constr.equal t 'xH
end.
Ltac2 gwt_is_zlit (t : constr) : bool :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f a => if Bool.or (Constr.equal f 'Zpos) (Constr.equal f 'Zneg) then gwt_is_pos (Array.get a 0) else false
| _ => Constr.equal t 'Z0
end.

Ltac2 rec gwt_zlist (l : constr) : constr list :=
match Constr.Unsafe.kind l with
| Constr.Unsafe.App f args => if Int.equal (Array.length args) 3 then Array.get args 1 :: gwt_zlist (Array.get args 2) else []
| Constr.Unsafe.Cast c _ _ => gwt_zlist c
| _ => []
end.

Ltac2 gwt_link (tb : constr) : constr :=
match Constr.Unsafe.kind tb with
| Constr.Unsafe.Constant k _ => if Constr.equal tb '@gwt_nil then tb else Std.eval_unfold [(Std.ConstRef k, Std.AllOccurrences)] tb
| _ => tb
end.

Ltac2 rec gwt_zcs (tb0 : constr) : (constr * constr) list :=
let tb := gwt_link tb0 in
match Constr.Unsafe.kind tb with
| Constr.Unsafe.App f args =>
if Bool.and (Constr.equal f '@gwt_zc) (Int.equal (Array.length args) 2) then
(Std.eval_vm None (Array.get args 0), Array.get args 0) :: gwt_zcs (Array.get args 1)
else if Int.equal (Array.length args) 3 then gwt_zcs (Array.get args 2)
else if Int.equal (Array.length args) 5 then gwt_zcs (Array.get args 4) else []
| _ => []
end.
Ltac2 rec gwt_assoc (v : constr) (l : (constr * constr) list) : constr option :=
match l with
| [] => None
| e :: tl => let (k, c) := e in if Constr.equal k v then Some c else gwt_assoc v tl
end.

Ltac2 rec gwt_fold_sums (lits : constr list) (zcs : (constr * constr) list) (t : constr) : constr :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f args =>
if Bool.and (Constr.equal f 'Z.add) (Bool.and (Int.equal (Array.length args) 2) (gwf_closed t)) then
(let v := Std.eval_vm None t in
match gwt_assoc v zcs with
| Some c => c
| None =>
if Bool.or (Bool.and (gwt_is_zlit (Array.get args 0)) (Constr.equal (Array.get args 1) 'Z0)) (List.exist (Constr.equal v) lits) then v
else Constr.Unsafe.map (gwt_fold_sums lits zcs) t
end)
else Constr.Unsafe.map (gwt_fold_sums lits zcs) t
| _ => Constr.Unsafe.map (gwt_fold_sums lits zcs) t
end.

Ltac2 gwt_unr0 (b : binder) : binder :=
match Constr.Binder.name b with
| Some id =>
if Ident.equal id @segs_ then Constr.Binder.make (Some @segs) (Constr.Binder.type b)
else if Ident.equal id @base_ then Constr.Binder.make (Some @base) (Constr.Binder.type b)
else b
| None => b
end.
Ltac2 rec gwt_rename (t : constr) : constr :=
let t := match Constr.Unsafe.kind t with
| Constr.Unsafe.Prod b c => Constr.Unsafe.make (Constr.Unsafe.Prod (gwt_unr0 b) c)
| Constr.Unsafe.Lambda b c => Constr.Unsafe.make (Constr.Unsafe.Lambda (gwt_unr0 b) c)
| Constr.Unsafe.LetIn b v c => Constr.Unsafe.make (Constr.Unsafe.LetIn (gwt_unr0 b) v c)
| _ => t
end in
Constr.Unsafe.map gwt_rename t.

Ltac2 rec gwt_ctx (t : constr) (ty : constr) : constr * constr :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod b rest =>
match Constr.Binder.name b with
| Some id =>
match Control.case (fun () => Control.hyp id) with
| Val p => let (h, _) := p in
match Control.case (fun () => constr:($t $h)) with
| Val q => let (th, _) := q in gwt_ctx th (Constr.Unsafe.substnl [h] 0 rest)
| Err _ => (t, ty)
end
| Err _ => (t, ty)
end
| None => (t, ty)
end
| Constr.Unsafe.Cast c _ _ => gwt_ctx t c
| _ => (t, ty)
end.

Ltac2 rec gwt_strip_prods (ty : constr) : constr :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod _ rest => gwt_strip_prods rest
| Constr.Unsafe.Cast c _ _ => gwt_strip_prods c
| _ => ty
end.
Ltac2 gwt_app_parts (t : constr) : constr * int :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App h args => (h, Array.length args)
| _ => (t, 0)
end.

Ltac2 gwt_eq_entry (c : constr) : (constr * int * constr) option :=
let body := gwt_strip_prods (Constr.type c) in
match Constr.Unsafe.kind body with
| Constr.Unsafe.App f args =>
if Bool.and (Constr.equal f '@eq) (Int.equal (Array.length args) 3) then
let (dh, dn) := gwt_app_parts (Array.get args 1) in
let (gh, gn) := gwt_app_parts (Array.get args 2) in
Some (gh, Int.sub gn dn, dh)
else None
| _ => None
end.
Ltac2 rec gwt_eq_group (g : ident list) : (constr * int * constr) list :=
match g with
| [] => []
| id :: rest =>
match Env.expand [id] with
| [] => gwt_eq_group rest
| rs => List.flat_map (fun r => match gwt_eq_entry (Env.instantiate r) with Some e => [e] | None => [] end) rs
end
end.
Ltac2 gwt_eq_table (gs : ident list list) : (constr * int * constr) list := List.flat_map gwt_eq_group gs.

Ltac2 gwt_head_ref (t : constr) : Std.reference list :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.Constant k _ => [Std.ConstRef k]
| _ => []
end.
Ltac2 rec gwt_nprod (ty : constr) : int :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod _ rest => Int.add 1 (gwt_nprod rest)
| Constr.Unsafe.Cast c _ _ => gwt_nprod c
| _ => 0
end.

Ltac2 rec gwt_unfolds (tb0 : constr) : Std.reference list :=
let tb := gwt_link tb0 in
match Constr.Unsafe.kind tb with
| Constr.Unsafe.App f args =>
if Int.equal (Array.length args) 2 then gwt_unfolds (Array.get args 1)
else if Int.equal (Array.length args) 3 then List.append (gwt_head_ref (Array.get args 1)) (gwt_unfolds (Array.get args 2))
else if Int.equal (Array.length args) 5 then gwt_unfolds (Array.get args 4) else []
| _ => []
end.

Ltac2 rec gwt_tables (tb0 : constr) : (constr * int * constr) list * (constr * constr) list :=
let tb := gwt_link tb0 in
match Constr.Unsafe.kind tb with
| Constr.Unsafe.App f args =>
if Int.equal (Array.length args) 2 then gwt_tables (Array.get args 1) else
if Int.equal (Array.length args) 3 then gwt_tables (Array.get args 2) else
if Int.equal (Array.length args) 5 then
let (ds, ps) := gwt_tables (Array.get args 4) in
let g := Array.get args 2 in
let d := Array.get args 3 in
if Constr.equal f '@gwt_def then
((g, Int.sub (gwt_nprod (Constr.type g)) (gwt_nprod (Constr.type d)), d) :: ds, ps)
else if Constr.equal f '@gwt_hdr then
let (gi, _) := gwt_ctx g (Constr.type g) in
let pat := gw2_value gi in
let (di, _) := gwt_ctx d (Constr.type d) in
(if Constr.equal pat di then (ds, ps) else (ds, (pat, di) :: ps))
else
let (gh, _) := gwt_app_parts g in
let (pi, _) := gwt_ctx g (Constr.type g) in
let pat := Std.eval_cbv { Std.rBeta := true; Std.rMatch := false; Std.rFix := false; Std.rCofix := false; Std.rZeta := false;
Std.rDelta := false; Std.rConst := gwt_head_ref gh; Std.rStrength := Std.Norm } pi in
let (di, _) := gwt_ctx d (Constr.type d) in
(ds, (pat, di) :: ps)
else ([], [])
| _ => ([], [])
end.

Ltac2 rec gwt_find (tbl : (constr * int * constr) list) (h : constr) : (int * constr) option :=
match tbl with
| [] => None
| e :: tl => let (g, k, d) := e in if Constr.equal g h then Some (k, d) else gwt_find tl h
end.
Ltac2 rec gwt_find_pat (ps : (constr * constr) list) (t : constr) : constr option :=
match ps with
| [] => None
| e :: tl => let (pat, d) := e in if Constr.equal pat t then Some d else gwt_find_pat tl t
end.
Ltac2 rec gwt_fold (tbl : (constr * int * constr) list) (ps : (constr * constr) list) (t : constr) : constr :=
match gwt_find_pat ps t with
| Some d => d
| None =>
match Constr.Unsafe.kind t with
| Constr.Unsafe.App h args =>
match gwt_find tbl h with
| Some p =>
let (k, d) := p in
let n := Array.length args in
if Int.lt n k then Constr.Unsafe.map (gwt_fold tbl ps) t
else if Int.equal n k then d
else Constr.Unsafe.make (Constr.Unsafe.App d (Array.map (gwt_fold tbl ps) (Array.sub args k (Int.sub n k))))
| None => Constr.Unsafe.map (gwt_fold tbl ps) t
end
| Constr.Unsafe.Constant _ _ => match gwt_find tbl t with Some p => let (k, d) := p in (if Int.equal k 0 then d else t) | None => t end
| Constr.Unsafe.Constructor _ _ => match gwt_find tbl t with Some p => let (k, d) := p in (if Int.equal k 0 then d else t) | None => t end
| _ => Constr.Unsafe.map (gwt_fold tbl ps) t
end
end.

Ltac2 gwt_finish (t1 : constr) (ty1 : constr) (gs : ident list list) (lits : constr) (pats : constr) : unit :=
let (_, ty2) := gwt_ctx t1 ty1 in
let ty3 := gwt_fold_sums (gwt_zlist lits) (gwt_zcs pats) ty2 in
let (ds, ps) := gwt_tables pats in
let ty4 := gwt_fold (List.append ds (gwt_eq_table gs)) [] ty3 in
let ty5 := match ps with [] => ty4 | _ => gwt_fold [] ps ty4 end in
let ty6 := match gwt_unfolds pats with
| [] => ty5
| us => Std.eval_unfold (List.map (fun r => (r, Std.AllOccurrences)) us) ty5
end in
gwf_exact (gwt_rename ty6).

Ltac2 ty2 (rep : constr) (t : constr) (gs : ident list list) (lits : constr) (pats : constr) : unit :=
let m := gw_mod_of rep in
let names := gw2_header_names t in
let (t1, ty1) := gw2_prefix m names t (Constr.type t) in
gwt_finish t1 ty1 gs lits pats.

Ltac2 ty1 (rep : constr) (t : constr) (gs : ident list list) (lits : constr) (pats : constr) : unit :=
let m := gw_mod_of rep in
let (t1, ty1) := gw_img_prefix m t (Constr.type t) in
gwt_finish t1 ty1 gs lits pats.

Ltac2 tyx (t : constr) (gs : ident list list) (lits : constr) (pats : constr) : unit :=
gwt_finish t (Constr.type t) gs lits pats.
