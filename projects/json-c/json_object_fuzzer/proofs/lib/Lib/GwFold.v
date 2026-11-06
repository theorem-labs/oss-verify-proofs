(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import GwApply.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require GwCallee.
From Ltac2 Require Import Ltac2 Constr Control.
From Ltac2 Require FMap FSet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".

Definition gw_ent {A : Type} (pat rep : A) (rest : unit) : unit := tt.

Definition gw_unhyp {P : Prop} (h : GwCallee.gw_hyp P) : P := h.

Definition gw_hidden (P : Prop) : Prop := P.
Ltac gw_hide H := lazymatch type of H with gw_hidden _ => idtac | ?T => change (gw_hidden T) in H end.

Ltac2 Type gwf_ent := constr * constr array * constr.
Ltac2 Type gwf_tbl := (constant, gwf_ent list) FMap.t * gwf_ent list.

Ltac2 rec gwf_table_acc (t : constr) (m : (constant, gwf_ent list) FMap.t) (o : gwf_ent list) : gwf_tbl :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App _ args =>
if Int.equal (Array.length args) 4 then
let pat := Array.get args 1 in
let rep := Array.get args 2 in
let (f, a) := match Constr.Unsafe.kind pat with
| Constr.Unsafe.App f a => (f, a)
| _ => (pat, Array.empty)
end in
match Constr.Unsafe.kind f with
| Constr.Unsafe.Constant k _ =>
let old := match FMap.find_opt k m with Some l => l | None => [] end in
gwf_table_acc (Array.get args 3) (FMap.add k (List.append old [(f, a, rep)]) m) o
| _ => gwf_table_acc (Array.get args 3) m (List.append o [(f, a, rep)])
end
else (m, o)
| Constr.Unsafe.Constant k _ => gwf_table_acc (Std.eval_unfold [(Std.ConstRef k, Std.AllOccurrences)] t) m o
| _ => (m, o)
end.
Ltac2 gwf_table (t : constr) : gwf_tbl := gwf_table_acc t (FMap.empty FSet.Tags.constant_tag) [].

Ltac2 rec gwf_prefix_eq (pa : constr array) (a : constr array) (i : int) : bool :=
if Int.equal i (Array.length pa) then true
else if Constr.equal (Array.get pa i) (Array.get a i) then gwf_prefix_eq pa a (Int.add i 1) else false.

Ltac2 rec gwf_find_l (tbl : gwf_ent list) (h : constr) (args : constr array) : (constr * int) option :=
match tbl with
| [] => None
| e :: tl =>
let (ph, pa, rep) := e in
if Int.le (Array.length pa) (Array.length args) then
(if Constr.equal h ph then (if gwf_prefix_eq pa args 0 then Some (rep, Array.length pa) else gwf_find_l tl h args)
else gwf_find_l tl h args)
else gwf_find_l tl h args
end.

Ltac2 gwf_find (tbl : gwf_tbl) (h : constr) (args : constr array) : (constr * int) option :=
let (m, o) := tbl in
let r := match Constr.Unsafe.kind h with
| Constr.Unsafe.Constant k _ => match FMap.find_opt k m with Some l => gwf_find_l l h args | None => None end
| _ => None
end in
match r with
| Some _ => r
| None => match o with [] => None | _ => gwf_find_l o h args end
end.

Ltac2 rec gwf_fold (tbl : gwf_tbl) (t : constr) : constr :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App h args =>
match gwf_find tbl h args with
| Some p =>
let (rep, k) := p in
let n := Array.length args in
if Int.equal k n then rep
else Constr.Unsafe.make (Constr.Unsafe.App rep (Array.map (gwf_fold tbl) (Array.sub args k (Int.sub n k))))
| None => Constr.Unsafe.map (gwf_fold tbl) t
end
| _ => Constr.Unsafe.map (gwf_fold tbl) t
end.

Ltac2 gwf_exact (t : constr) : unit := ltac1:(t |- exact t) (Ltac1.of_constr t).

Ltac2 gwf_head_ref (t : constr) : Std.reference :=
let h := match Constr.Unsafe.kind t with Constr.Unsafe.App f _ => f | _ => t end in
match Constr.Unsafe.kind h with
| Constr.Unsafe.Constant k _ => Std.ConstRef k
| _ => Control.throw (Tactic_failure (Some (Message.of_string "gw_rebind: the term is not an applied constant")))
end.

Ltac2 gw_rebind0 (t : constr) (tb : constr) : unit :=
let r := gwf_head_ref t in
let b := Std.eval_cbv { Std.rBeta := true; Std.rMatch := false; Std.rFix := false; Std.rCofix := false; Std.rZeta := false;
Std.rDelta := false; Std.rConst := [r]; Std.rStrength := Std.Norm } t in
gwf_exact (gwf_fold (gwf_table tb) b).
Ltac gw_rebind t tb := let f := ltac2:(t tb |- gw_rebind0 (Option.get (Ltac1.to_constr t)) (Option.get (Ltac1.to_constr tb))) in f t tb.

Ltac2 gw_rebind_ty0 (t : constr) (tb : constr) : unit := gwf_exact (gwf_fold (gwf_table tb) (Constr.type t)).
Ltac gw_rebind_ty t tb := let f := ltac2:(t tb |- gw_rebind_ty0 (Option.get (Ltac1.to_constr t)) (Option.get (Ltac1.to_constr tb))) in f t tb.
Ltac2 gw_rebind_tm0 (t : constr) (tb : constr) : unit :=
let r := gwf_head_ref t in
let b := Std.eval_cbv { Std.rBeta := true; Std.rMatch := false; Std.rFix := false; Std.rCofix := false; Std.rZeta := false;
Std.rDelta := false; Std.rConst := [r]; Std.rStrength := Std.Norm } t in
Std.exact_no_check (gwf_fold (gwf_table tb) b).
Ltac gw_rebind_tm t tb := let f := ltac2:(t tb |- gw_rebind_tm0 (Option.get (Ltac1.to_constr t)) (Option.get (Ltac1.to_constr tb))) in f t tb.

Ltac2 gw_fold_exact0 (t : constr) (tb : constr) : unit := gwf_exact (gwf_fold (gwf_table tb) t).
Ltac gw_fold_exact t tb := let f := ltac2:(t tb |- gw_fold_exact0 (Option.get (Ltac1.to_constr t)) (Option.get (Ltac1.to_constr tb))) in f t tb.

Ltac2 rec gwf_ctx_args (ty : constr) (acc : constr list) : constr list * constr :=
match Constr.Unsafe.kind ty with
| Constr.Unsafe.Prod b rest =>
match Constr.Binder.name b with
| Some id =>
match Control.case (fun () => Control.hyp id) with
| Val p => let (h, _) := p in gwf_ctx_args rest (h :: acc)
| Err _ => (acc, ty)
end
| None => (acc, ty)
end
| _ => (acc, ty)
end.
Ltac2 gw_ctx_app (t : constr) : constr * constr :=
let (acc, rest) := gwf_ctx_args (Constr.type t) [] in
let r := match acc with
| [] => t
| _ :: _ => Constr.Unsafe.make (Constr.Unsafe.App t (Array.of_list (List.rev acc)))
end in
(r, Constr.Unsafe.substnl acc 0 rest).

Ltac2 gw_ctx_fold_ty0 (t : constr) (tb : constr) : unit := let (_, ty) := gw_ctx_app t in gwf_exact (gwf_fold (gwf_table tb) ty).
Ltac gw_ctx_fold_ty t tb := let f := ltac2:(t tb |- gw_ctx_fold_ty0 (Option.get (Ltac1.to_constr t)) (Option.get (Ltac1.to_constr tb))) in f t tb.
Ltac2 gw_ctx_fold_tm0 (t : constr) : unit := let (r, _) := gw_ctx_app t in Std.exact_no_check r.
Ltac gw_ctx_fold_tm t := let f := ltac2:(t |- gw_ctx_fold_tm0 (Option.get (Ltac1.to_constr t))) in f t.

Ltac2 gw_ctx_fold0 (t : constr) (tb : constr) : unit :=
let (r, ty0) := gw_ctx_app t in
let ty := gwf_fold (gwf_table tb) ty0 in
gwf_exact (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.default ty)).
Ltac gw_ctx_fold t tb := let f := ltac2:(t tb |- gw_ctx_fold0 (Option.get (Ltac1.to_constr t)) (Option.get (Ltac1.to_constr tb))) in f t tb.

Ltac2 rec gwf_closed (t : constr) : bool :=
match Constr.Unsafe.kind t with
| Constr.Unsafe.App f args => if gwf_closed f then Array.for_all gwf_closed args else false
| Constr.Unsafe.Constant _ _ => true
| Constr.Unsafe.Constructor _ _ => true
| Constr.Unsafe.Ind _ _ => true
| _ => false
end.
Ltac gw_is_closed c := let f := ltac2:(c |- if gwf_closed (Option.get (Ltac1.to_constr c)) then () else Control.zero (Tactic_failure None)) in f c.
Ltac gw_is_zlit c := lazymatch c with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac gw_rom_norm :=
repeat match goal with
| ROM : ro_bytes _ ?g _ |- context [Z.add ?g ?c] =>
tryif gw_is_zlit c then fail else (gw_is_closed c; let v := eval cbv in c in change (Z.add g c) with (Z.add g v))
| ROM : ro_bytes _ ?g _ |- context [Z.add ?c ?g] =>
gw_is_closed c; let v := eval cbv in c in change (Z.add c g) with (Z.add v g); rewrite (Z.add_comm v g)
end.
Ltac gw_pc_norm :=
lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?e) _ _ _ _) =>
tryif is_var e then replace (Z_to_bv 64 e) with (Z_to_bv 64 (e + 0)%Z) by (rewrite Z.add_0_r; reflexivity) else idtac
| _ => idtac
end.
